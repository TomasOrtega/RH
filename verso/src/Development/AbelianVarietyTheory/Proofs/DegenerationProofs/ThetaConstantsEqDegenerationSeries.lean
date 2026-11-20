import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultiple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisingFactorStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.Ex.ThetaSeries
open GlobalTheory.UT GlobalTheory.UT.SymFrame ReciprocityTheory.ChartRestriction.G.DVR

/- English proof (translation)
Use `letI : Module R C := Module.compHom C (algebraMap R (FractionRing R))`. Set `φ : R →+* C` to `(algebraMap (FractionRing R) C).comp (algebraMap R _)`. Establish `hφ : ∀ (a : R) (y : C), a • y = φ a * y` using `fun a y => Algebra.smul_def (algebraMap R (FractionRing R) a) y`. Establish `bd : ∀ {E : Type} [AddCommGroup E] [Module R E] (f : E →+ C), (∀ (a : R) y, f (a • y) = φ a * f y) → ∀ (t : Set E) (c : ℝ), 0 ≤ c → (∀ y ∈ t, ‖f y‖ ≤ c) → ∀ y ∈ Submodule.span R t, ‖f y‖ ≤ c`. Introduce `E _ _ f hf t c h0 hc y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact hc y hy`. Consider the case `zero => simpa using h0`. Consider the case `add y z _ _ h1 h2 => rw [map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)`.

Consider the case `smul a y _ h1 => rw [hf, norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (hC.1 a)).trans h1`. Take `⟨N, ⟨t, rfl⟩, -, -, h⟩` from `h`. Take `⟨u, rfl⟩` from `IsNoetherian.noetherian I`. Take `⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ y ∈ t, ‖y‖ ≤ c` from `⟨∑ y ∈ t, ‖y‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun y hy => Finset.single_le_sum (f := fun y : C => ‖y‖) (fun _ _ => norm_nonneg _) hy⟩`.

Take `⟨r, hr0, hr1, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ a ∈ u, ‖φ a‖ ≤ r` from `⟨(u.sup fun a => ‖φ a‖₊ : NNReal), NNReal.coe_nonneg _, by exact_mod_cast (Finset.sup_lt_iff (f := fun a => ‖φ a‖₊) (zero_lt_one' NNReal)).2 fun a ha => show ‖φ a‖₊ < 1 from hC.2 a (Submodule.subset_span ha), fun a ha => by exact_mod_cast Finset.le_sup (f := fun a => ‖φ a‖₊) ha⟩`. Establish `hI` using `bd φ.toAddMonoidHom (fun a y => map_mul φ a y) u r hr0 hr`. Establish `hP : ∀ n : ℕ, ∀ y ∈ (Submodule.span R (u : Set R)) ^ n • Submodule.span R (t : Set C), ‖y‖ ≤ r ^ n * c`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simpa using bd (AddMonoidHom.id C) hφ t c hc0 hc`. Consider the case `succ n ih`. Introduce `y hy`. Rewrite `hy` using `[pow_succ', Submodule.mul_smul]`. Use `Submodule.smul_induction_on hy (fun a ha z hz => ?_) (fun y z h1 h2 => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2))` and prove the remaining obligations.

Rewrite using `[hφ, norm_mul, pow_succ', _root_.mul_assoc]`. Conclude with `mul_le_mul (hI a ha) (ih z hz) (norm_nonneg _) hr0`. Use `Metric.tendsto_nhds.2 fun e he => ?_` and prove the remaining obligations. Establish `lim` using `(tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const c`. Rewrite `lim` using `[zero_mul]`.

Take `⟨n, hn⟩` from `(lim.eventually (gt_mem_nhds he)).exists`. Take `⟨S, hS⟩` from `h n`. Use `Filter.mem_of_superset (Filter.mem_atTop S) fun T hT => ?_` and prove the remaining obligations. Use `show dist _ _ < e`. Rewrite using `[dist_comm, dist_eq_norm]`.

Conclude with `(hP n _ (hS T hT)).trans_lt hn`.
-/
theorem hasSum_of_sumF {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {I : Ideal R} {C : Type} [NormedField C]
    [IsUltrametricDist C] [Algebra (FractionRing R) C] (hC : CExt R I C) {Ix : Type} {x : Ix → C} {s : C}
    (h : SumF I C x s) : HasSum x s := by
  letI : Module R C := Module.compHom C (algebraMap R (FractionRing R))
  let φ : R →+* C := (algebraMap (FractionRing R) C).comp (algebraMap R _)
  have hφ : ∀ (a : R) (y : C), a • y = φ a * y := fun a y => Algebra.smul_def (algebraMap R (FractionRing R) a) y
  have bd : ∀ {E : Type} [AddCommGroup E] [Module R E] (f : E →+ C), (∀ (a : R) y, f (a • y) = φ a * f y) →
      ∀ (t : Set E) (c : ℝ), 0 ≤ c → (∀ y ∈ t, ‖f y‖ ≤ c) → ∀ y ∈ Submodule.span R t, ‖f y‖ ≤ c := by
    intro E _ _ f hf t c h0 hc y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hc y hy
    | zero => simpa using h0
    | add y z _ _ h1 h2 => rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
    | smul a y _ h1 => rw [hf, norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (hC.1 a)).trans h1
  obtain ⟨N, ⟨t, rfl⟩, -, -, h⟩ := h
  obtain ⟨u, rfl⟩ := IsNoetherian.noetherian I
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ y ∈ t, ‖y‖ ≤ c :=
    ⟨∑ y ∈ t, ‖y‖, Finset.sum_nonneg fun _ _ => norm_nonneg _,
      fun y hy => Finset.single_le_sum (f := fun y : C => ‖y‖) (fun _ _ => norm_nonneg _) hy⟩
  obtain ⟨r, hr0, hr1, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ a ∈ u, ‖φ a‖ ≤ r :=
    ⟨(u.sup fun a => ‖φ a‖₊ : NNReal), NNReal.coe_nonneg _,
      by exact_mod_cast (Finset.sup_lt_iff (f := fun a => ‖φ a‖₊) (zero_lt_one' NNReal)).2 fun a ha =>
        show ‖φ a‖₊ < 1 from hC.2 a (Submodule.subset_span ha),
      fun a ha => by exact_mod_cast Finset.le_sup (f := fun a => ‖φ a‖₊) ha⟩
  have hI := bd φ.toAddMonoidHom (fun a y => map_mul φ a y) u r hr0 hr
  have hP : ∀ n : ℕ, ∀ y ∈ (Submodule.span R (u : Set R)) ^ n • Submodule.span R (t : Set C), ‖y‖ ≤ r ^ n * c := by
    intro n
    induction n with
    | zero => simpa using bd (AddMonoidHom.id C) hφ t c hc0 hc
    | succ n ih =>
      intro y hy
      rw [pow_succ', Submodule.mul_smul] at hy
      refine Submodule.smul_induction_on hy (fun a ha z hz => ?_)
        (fun y z h1 h2 => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2))
      rw [hφ, norm_mul, pow_succ', _root_.mul_assoc]
      exact mul_le_mul (hI a ha) (ih z hz) (norm_nonneg _) hr0
  refine Metric.tendsto_nhds.2 fun e he => ?_
  have lim := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const c
  rw [zero_mul] at lim
  obtain ⟨n, hn⟩ := (lim.eventually (gt_mem_nhds he)).exists
  obtain ⟨S, hS⟩ := h n
  refine Filter.mem_of_superset (Filter.mem_atTop S) fun T hT => ?_
  show dist _ _ < e
  rw [dist_comm, dist_eq_norm]
  exact (hP n _ (hS T hT)).trans_lt hn

section Alg

variable {A A' U U' : Type} [CommGroup A] [CommGroup A'] [CommGroup U] [CommGroup U'] {θ : A → A → A → U}
  {θ' : A' → A' → A' → U'} {σ : A → U} {σ' : A' → U'}

/- English proof (translation)
Simplify using `only [cubN, map_prod, _root_.one_mul, ← map_pow, h]`.
-/
theorem cubN_map (e : A →* A') (f : U →* U') (h : ∀ x y u, θ' (e x) (e y) (e u) = f (θ x y u)) (k : ℕ) (b x : A) :
    cubN θ' k 1 (e b) (e x) = f (cubN θ k 1 b x) := by
  simp only [cubN, map_prod, _root_.one_mul, ← map_pow, h]

/- English proof (translation)
Simplify using `only [dbl, map_div, ← map_inv e, h, h']`.
-/
theorem dbl_map (e : A →* A') (f : U →* U') (h : ∀ x y u, θ' (e x) (e y) (e u) = f (θ x y u))
    (h' : ∀ x, σ' (e x) = f (σ x)) (x : A) : dbl θ' σ' (e x) = f (dbl θ σ x) := by
  simp only [dbl, map_div, ← map_inv e, h, h']

/- English proof (translation)
Simplify using `only [mulq, map_prod, map_div, map_pow f, cubN_map e f h, dbl_map e f h h']`.
-/
theorem mulq_map (e : A →* A') (f : U →* U') (h : ∀ x y u, θ' (e x) (e y) (e u) = f (θ x y u))
    (h' : ∀ x, σ' (e x) = f (σ x)) (k : ℕ) (x : A) : mulq θ' σ' k (e x) = f (mulq θ σ k x) := by
  simp only [mulq, map_prod, map_div, map_pow f, cubN_map e f h, dbl_map e f h h']

end Alg

section Univ

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

abbrev symV (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι)
    (x : T ⟶ D.P.A) : (T.left.presheaf.stalk z)ˣ := val D.sym x.left z J

/- English proof (translation)
The claim follows from `((grep_cubN (D := D) (𝟙 _) (𝟙 _) n).mul (((grep_cub (D := D) (𝟙 _) (𝟙 _)⁻¹ (𝟙 _)).mul (grep_sym (𝟙 _)).inv).pow n).inv).congr (fun U _ h => by simp only [mul_inv_cancel, inv_mul_cancel, _root_.one_mul, ← pow_succ] apply Additive.ofMul.injective simp only [ofMul_mul, ofMul_inv, of …`.
-/
theorem grep_step (n : ℕ) : GRep D.P.L D.P.A
    (fun _ _ h => h (𝟙 D.P.A ^ (n + 1)).left * (h (𝟙 D.P.A ^ n).left)⁻¹ * (h (𝟙 D.P.A :).left ^ (2 * n + 1))⁻¹ *
      h (1 : D.P.A ⟶ D.P.A).left ^ (2 * n + 1))
    (fun _ r z J => cubN (cubV D.cub z J) n 1 r r / dbl (cubV D.cub z J) (symV D z J) r ^ n) :=
  ((grep_cubN (D := D) (𝟙 _) (𝟙 _) n).mul
    (((grep_cub (D := D) (𝟙 _) (𝟙 _)⁻¹ (𝟙 _)).mul (grep_sym (𝟙 _)).inv).pow n).inv).congr
    (fun U _ h => by
      simp only [mul_inv_cancel, inv_mul_cancel, _root_.one_mul, ← pow_succ]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      module)
    (fun T r z J _ => by
      have e : r ≫ (𝟙 D.P.A)⁻¹ = r⁻¹ := (map_inv (preHom (G := D.P.A) r) _).trans (congrArg (·⁻¹) (Category.comp_id r))
      simp only [dbl, e, Category.comp_id, div_eq_mul_inv])

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ((grep_sym (𝟙 _)).pow 0).congr (fun U _ h => by simp) (fun _ _ _ _ _ => by simp [mulq])`. Consider the case `succ n ih`. Use `(ih.mul (grep_step n)).congr (fun U _ h => ?_) (fun _ _ _ _ _ => (Finset.prod_range_succ _ _).symm)` and prove the remaining obligations. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv, ofMul_pow]`. Use `module`.
-/
theorem grep_mulq (n : ℕ) : GRep D.P.L D.P.A
    (fun _ _ h => h (𝟙 D.P.A ^ n).left * (h (𝟙 D.P.A :).left ^ (n ^ 2))⁻¹ * h (1 : D.P.A ⟶ D.P.A).left ^ (n ^ 2) *
      (h (1 : D.P.A ⟶ D.P.A).left)⁻¹)
    (fun _ r z J => mulq (cubV D.cub z J) (symV D z J) n r) := by
  induction n with
  | zero => exact ((grep_sym (𝟙 _)).pow 0).congr (fun U _ h => by simp) (fun _ _ _ _ _ => by simp [mulq])
  | succ n ih =>
    refine (ih.mul (grep_step n)).congr (fun U _ h => ?_) (fun _ _ _ _ _ => (Finset.prod_range_succ _ _).symm)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module

/- English proof (translation)
Establish `C : IsCub (cubV D.cub (T` using `T) z J) := isCub_cubV D.cub hJ`. Rewrite using `[C.N_one, dbl, C.face, symV, normd_one (u := D.sym) ⟨D.sym_gen, D.sym_rig⟩ hJ]`. Simplify using the standard rewrite rules.
-/
theorem step_one (n : ℕ) {T : Over (Spec (CommRingCat.of R))} {z : T.left} {J} (hJ : Good D.P.L z J) :
    cubN (cubV D.cub z J) n 1 1 1 / dbl (cubV D.cub z J) (symV D z J) 1 ^ n = 1 := by
  have C : IsCub (cubV D.cub (T := T) z J) := isCub_cubV D.cub hJ
  rw [C.N_one, dbl, C.face, symV, normd_one (u := D.sym) ⟨D.sym_gen, D.sym_rig⟩ hJ]
  simp

/- English proof (translation)
Establish `key` using `((grep_nu ν hν.1 (𝟙 _)).mul (grep_step n).inv).triv hG (fun U _ h => by`. Rewrite using `[← pow_succ]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]`. Use the proof step `module)`.

Use the proof step `(fun y J hJ => by beta_reduce`. Rewrite using `[Category.comp_id, normd_one hν hJ, step_one n hJ, inv_one, _root_.mul_one]) T b z J hJ`. Use `beta_reduce at key`. Rewrite `key` using `[Category.comp_id]`. Conclude with `mul_inv_eq_one.1 key`.
-/
theorem val_nu (hG : GlobalFnsSt) {n : ℕ} {ν : LB.Gen (nuLB D n)} (hν : Normd ν) {T : Over (Spec (CommRingCat.of R))}
    (b : T ⟶ D.P.A) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val ν b.left z J = cubN (cubV D.cub z J) n 1 b b / dbl (cubV D.cub z J) (symV D z J) b ^ n := by
  have key := ((grep_nu ν hν.1 (𝟙 _)).mul (grep_step n).inv).triv hG (fun U _ h => by
      rw [← pow_succ]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (fun y J hJ => by
      beta_reduce
      rw [Category.comp_id, normd_one hν hJ, step_one n hJ, inv_one, _root_.mul_one]) T b z J hJ
  beta_reduce at key
  rw [Category.comp_id] at key
  exact mul_inv_eq_one.1 key

/- English proof (translation)
Establish `key` using `((grep_kap κ hκ.1 (𝟙 _)).mul (grep_mulq n)).triv hG (fun U _ h => by`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]`. Use the proof step `module)`. Use the proof step `(fun y J hJ => by beta_reduce`.

Rewrite using `[Category.comp_id, normd_one hκ hJ, _root_.one_mul]`. Conclude with `Finset.prod_eq_one fun i _ => step_one i hJ) T b z J hJ`. Use `beta_reduce at key`. Rewrite `key` using `[Category.comp_id]`. Then use the resulting hypothesis.
-/
theorem val_kap (hG : GlobalFnsSt) {n : ℕ} {κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1)} (hκ : Normd κ)
    {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val κ b.left z J * mulq (cubV D.cub z J) (symV D z J) n b = 1 := by
  have key := ((grep_kap κ hκ.1 (𝟙 _)).mul (grep_mulq n)).triv hG (fun U _ h => by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (fun y J hJ => by
      beta_reduce
      rw [Category.comp_id, normd_one hκ hJ, _root_.one_mul]
      exact Finset.prod_eq_one fun i _ => step_one i hJ) T b z J hJ
  beta_reduce at key
  rwa [Category.comp_id] at key

end Univ

section Values

open CoefBasic

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N) (y : (TF (R := R) F).left)

def sU : Fˣ →* ((TF (R := R) F).left.presheaf.stalk y)ˣ := Units.map (cstH (R := R) (F := F) y).toMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sU_val (u : Fˣ) : (sU y u).val = cstH y u := rfl

/- English proof (translation)
Introduce `_ _ h` and use `Units.ext (cstH_inj y (congrArg Units.val h))`.
-/
theorem sU_inj : Function.Injective (sU (R := R) (F := F) y) := fun _ _ h =>
  Units.ext (cstH_inj y (congrArg Units.val h))

/- English proof (translation)
Introduce `ψ` and use `ν.good ψ trivial`.
-/
theorem good : Good D.P.L y ν.J := fun ψ => ν.good ψ trivial

/- English proof (translation)
The claim follows from `toStk_valF (F := F) r _ y ((good ν y).mem φ r) _`.
-/
theorem c_vF {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : (TF (R := R) F).left ⟶ Y) :
    cstH y (vF (F := F) t r ν.J) = (val t r y ν.J).val := toStk_valF (F := F) r _ y ((good ν y).mem φ r) _

/- English proof (translation)
Establish `h` using `(good ν y).mem φ r`. Establish `h'` using `(top_le_iff_mem (F := F) r _ y).2 h`. Use `(congrArg (cstH y) (dif_pos h')).trans (Eq.trans ?_ (gs_eq r y _ h _).symm)` and prove the remaining obligations. Use `show ((Sp F).presheaf.germ ⊤ y trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _`. Rewrite using `[Iso.hom_inv_id_apply]`.

Conclude with `TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE h') y trivial _`.
-/
theorem c_sF {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb D.P.L φ ε)) (r : (TF (R := R) F).left ⟶ Y) :
    cstH y (sF (F := F) s r ν.J) = sval s r y ν.J := by
  have h := (good ν y).mem φ r
  have h' := (top_le_iff_mem (F := F) r _ y).2 h
  refine (congrArg (cstH y) (dif_pos h')).trans (Eq.trans ?_ (gs_eq r y _ h _).symm)
  show ((Sp F).presheaf.germ ⊤ y trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE h') y trivial _

/- English proof (translation)
The claim follows from `c_vF ν y (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig _`.
-/
theorem c_rg : cstH y ν.rg = (rigV D (TF (R := R) F).hom y ν.J).val :=
  c_vF ν y (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig _

/- English proof (translation)
The claim follows from `Units.ext ((c_vF ν y _ _).symm.trans (congrArg (cstH y) (ν.θ_eq a b d).symm))`.
-/
theorem cubV_eq (a b d : N.A) : cubV D.cub y ν.J (ν.eA a) (ν.eA b) (ν.eA d) = sU y (N.θ a b d) :=
  Units.ext ((c_vF ν y _ _).symm.trans (congrArg (cstH y) (ν.θ_eq a b d).symm))

/- English proof (translation)
The claim follows from `Units.ext ((c_vF ν y _ _).symm.trans (congrArg (cstH y) (ν.σ_eq a).symm))`.
-/
theorem sym_eq (a : N.A) : symV D y ν.J (ν.eA a) = sU y (N.σ a) :=
  Units.ext ((c_vF ν y _ _).symm.trans (congrArg (cstH y) (ν.σ_eq a).symm))

/- English proof (translation)
The claim follows from `Units.ext ((c_vF ν y _ _).symm.trans (congrArg (cstH y) (h.2 χ).symm))`.
-/
theorem pt_val {g : GtPtF D F} {c : N.Gt} (h : ν.Pt g c) (χ : N.X) :
    val (g.s (ν.eX χ)) (𝟙 _) y ν.J = sU y (c.s χ) :=
  Units.ext ((c_vF ν y _ _).symm.trans (congrArg (cstH y) (h.2 χ).symm))

/- English proof (translation)
Introduce `α x`. Take `⟨y⟩` from `exists_pt (R := R) (F := F)`. Establish `hm` using `(good ν y).mem (DegPre.famφ D F (ν.eX α)) (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left`. Establish `e` using `sval_lin (ν.eA x) s 0 c (ν.eX α) (good ν y)`. Establish `z : sval ((0 : Fam D F k).s (ν.eX α)) (lift (𝟙 (TF (R` using `R) F)) (ν.eA x)).left y ν.J = 0 := (gs_eq _ y _ hm _).trans ((congrArg _ (map_zero _)).trans (map_zero _))`.

Rewrite `e` using `[add_zero, z, add_zero, cst_eq, ← c_sF, ← c_sF, ← map_mul, ← h α x]`. Conclude with `(_root_.mul_assoc _ _ _).trans (cstH_inj y e).symm`.
-/
theorem famV_smul {k : ℕ} {s : Fam D F k} {f : N.X → N.A → F} (h : ν.FamV s f) (c : F) : ν.FamV (c • s) (c • f) := by
  intro α x
  obtain ⟨y⟩ := exists_pt (R := R) (F := F)
  have hm := (good ν y).mem (DegPre.famφ D F (ν.eX α)) (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left
  have e := sval_lin (ν.eA x) s 0 c (ν.eX α) (good ν y)
  have z : sval ((0 : Fam D F k).s (ν.eX α)) (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left y ν.J = 0 :=
    (gs_eq _ y _ hm _).trans ((congrArg _ (map_zero _)).trans (map_zero _))
  rw [add_zero, z, add_zero, cst_eq, ← c_sF, ← c_sF, ← map_mul, ← h α x] at e
  exact (_root_.mul_assoc _ _ _).trans (cstH_inj y e).symm

/- English proof (translation)
Establish `hJ` using `good ν y`. Take `⟨n, hn⟩` from `exists_nu (D := D) hL.mulPull k`. Take `⟨κ, hκ⟩` from `exists_kap (D := D) hL.mulPull k`. Set `u : Fˣ` to `Units.mk0 (vF (F := F) w (𝟙 _) ν.J) fun h => Units.ne_zero _ ((c_vF ν y w _).symm.trans ((congrArg (cstH y) h).trans (map_zero _)))`. Establish `hu : val w (𝟙 _) y ν.J = sU y u` using `Units.ext (c_vF ν y w _).symm`.

Establish `a₁` using `hw.2.1 n hn y _ hJ`. Establish `a₂` using `hw.2.2 κ hκ y _ hJ`. Establish `b₁` using `val_nu hL.globalFns hn p.g.b hJ`. Establish `b₂` using `val_kap hL.globalFns hκ p.g.b hJ`. Establish `hb : p.g.b = ν.eA.toMonoidHom q.1.2.b` using `hq.2.1.symm`.

Establish `c₁ : val (p.g.s p.y) (𝟙 _) y ν.J = sU y (q.1.2.s q.1.1.toAdd)`. Rewrite using `[← hq.1]`. Conclude with `pt_val ν y hq.2 _`. Establish `c₂ : @id ((TF (R` using `R) F).left.presheaf.stalk y)ˣ (val (D.psi p.y) (jFK (R := R) F) y ν.J) * rigV D (TF (R := R) F).hom y ν.J = sU y (N.ψ q.1.1.toAdd) := by`. Rewrite using `[← hq.1]`.

Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[sU_val, ν.ψ_eq, map_mul]`. Conclude with `congrArg₂ (· * ·) (c_vF ν y _ _).symm (c_rg ν y).symm`. Rewrite `a₁` using `[b₁, hu, c₁]`. Rewrite `a₂` using `[c₂, hu, eq_inv_of_mul_eq_one_left b₂]`.

Rewrite `a₁` using `[hb, cubN_map _ (sU y) (cubV_eq ν y), dbl_map _ (sU y) (cubV_eq ν y) (sym_eq ν y)]`. Rewrite `a₂` using `[hb, mulq_map _ (sU y) (cubV_eq ν y) (sym_eq ν y)]`. Rewrite using `[hu, ((GlobalTheory.T.wQ_characterization_and_mul_relation F N k hk q q).1 u).2 ⟨sU_inj y ?_, sU_inj y ?_⟩]`. Rewrite using `[NumD.tk, map_mul, map_mul, map_pow, map_pow, a₁, _root_.mul_assoc, div_mul_cancel]`. Rewrite using `[map_mul, map_pow, ← a₂, inv_mul_cancel_right]`.
-/
theorem val_frame [IsNoetherianRing R] (hL : Laws) {k : ℕ} (hk : Odd k) {p : QkPt D F k} {q : N.QT k} (hq : ν.QPt p q)
    {w} (hw : TXFrame k p w) : val w (𝟙 _) y ν.J = sU y (N.wQ q) := by
  have hJ := good ν y
  obtain ⟨n, hn⟩ := exists_nu (D := D) hL.mulPull k
  obtain ⟨κ, hκ⟩ := exists_kap (D := D) hL.mulPull k
  let u : Fˣ := Units.mk0 (vF (F := F) w (𝟙 _) ν.J) fun h =>
    Units.ne_zero _ ((c_vF ν y w _).symm.trans ((congrArg (cstH y) h).trans (map_zero _)))
  have hu : val w (𝟙 _) y ν.J = sU y u := Units.ext (c_vF ν y w _).symm
  have a₁ := hw.2.1 n hn y _ hJ
  have a₂ := hw.2.2 κ hκ y _ hJ
  have b₁ := val_nu hL.globalFns hn p.g.b hJ
  have b₂ := val_kap hL.globalFns hκ p.g.b hJ
  have hb : p.g.b = ν.eA.toMonoidHom q.1.2.b := hq.2.1.symm
  have c₁ : val (p.g.s p.y) (𝟙 _) y ν.J = sU y (q.1.2.s q.1.1.toAdd) := by
    rw [← hq.1]; exact pt_val ν y hq.2 _
  have c₂ : @id ((TF (R := R) F).left.presheaf.stalk y)ˣ (val (D.psi p.y) (jFK (R := R) F) y ν.J) *
      rigV D (TF (R := R) F).hom y ν.J = sU y (N.ψ q.1.1.toAdd) := by
    rw [← hq.1]
    refine Units.ext ?_
    rw [sU_val, ν.ψ_eq, map_mul]
    exact congrArg₂ (· * ·) (c_vF ν y _ _).symm (c_rg ν y).symm
  rw [b₁, hu, c₁] at a₁
  rw [c₂, hu, eq_inv_of_mul_eq_one_left b₂] at a₂
  rw [hb, cubN_map _ (sU y) (cubV_eq ν y), dbl_map _ (sU y) (cubV_eq ν y) (sym_eq ν y)] at a₁
  rw [hb, mulq_map _ (sU y) (cubV_eq ν y) (sym_eq ν y)] at a₂
  rw [hu, ((GlobalTheory.T.wQ_characterization_and_mul_relation F N k hk q q).1 u).2 ⟨sU_inj y ?_, sU_inj y ?_⟩]
  · rw [NumD.tk, map_mul, map_mul, map_pow, map_pow, a₁, _root_.mul_assoc, div_mul_cancel]
  · rw [map_mul, map_pow, ← a₂, inv_mul_cancel_right]

/- English proof (translation)
Take `⟨y⟩` from `exists_pt (R := R) (F := F)`. Establish `hJ` using `good ν y`. Establish `a` using `isCoef_coef g' hw' (ν.eX α) ϑ y _ hJ`. Establish `b` using `val_kap hL.globalFns hκ p.g.b hJ`. Establish `hb : p.g.b = ν.eA.toMonoidHom q.1.2.b` using `hq.2.1.symm`.

Establish `e` using `hv y _ hJ`. Rewrite `e` using `[val_frame ν y hL hm.pow hq hw, eq_inv_of_mul_eq_one_left b, hb, mulq_map _ (sU y) (cubV_eq ν y) (sym_eq ν y), ← map_inv, ← map_mul]`. Establish `f` using `congrArg (cstH y) (hϑ α (q.1.2 ^ m).b)`. Rewrite `f` using `[c_sF, hg'.1, map_mul, map_pow, c_rg]`. Rewrite `a` using `[← e, pt_val ν y hg', ← f, cst_eq, sU_val, sU_val, pow_one, mul_right_comm _ (Units.val _), mul_right_comm _ (Units.val _), Units.mul_left_inj, ← map_mul, ← map_mul]`.

Rewrite using `[cstH_inj y a, NumD.txT, NumD.vt, mul_comm (N.c α), div_eq_mul_inv]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, NumD.vth, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coef_eq_txT [IsNoetherianRing R] (hL : Laws) {m : ℕ} (hm : Odd m) {p : QkPt D F (m ^ 2)} {q : N.QT (m ^ 2)}
    (hq : ν.QPt p q) {w} (hw : TXFrame (m ^ 2) p w) {g' : GtPtF D F} (hg' : ν.Pt g' (q.1.2 ^ m))
    {κ : LB.Gen (kapLB D (𝟙 D.P.A ^ m) (m ^ 2) 1)} (hκ : Normd κ) {w' : Frm D F 1 g'.b} (hw' : w'.IsGen)
    (hv : ∀ z J, Good D.P.L z J → val w (𝟙 _) z J * val κ p.g.b.left z J = val w' (𝟙 _) z J)
    {ϑ : Fam D F 1} {c : F} (hϑ : ν.FamV ϑ (c • N.vth)) (α : N.X) : coef ϑ g' w' (ν.eX α) = c * N.txT m q α := by
  obtain ⟨y⟩ := exists_pt (R := R) (F := F)
  have hJ := good ν y
  have a := isCoef_coef g' hw' (ν.eX α) ϑ y _ hJ
  have b := val_kap hL.globalFns hκ p.g.b hJ
  have hb : p.g.b = ν.eA.toMonoidHom q.1.2.b := hq.2.1.symm
  have e := hv y _ hJ
  rw [val_frame ν y hL hm.pow hq hw, eq_inv_of_mul_eq_one_left b, hb, mulq_map _ (sU y) (cubV_eq ν y) (sym_eq ν y),
    ← map_inv, ← map_mul] at e
  have f := congrArg (cstH y) (hϑ α (q.1.2 ^ m).b)
  rw [c_sF, hg'.1, map_mul, map_pow, c_rg] at f
  rw [← e, pt_val ν y hg', ← f, cst_eq, sU_val, sU_val, pow_one, mul_right_comm _ (Units.val _), mul_right_comm _ (Units.val _),
    Units.mul_left_inj, ← map_mul, ← map_mul] at a
  rw [cstH_inj y a, NumD.txT, NumD.vt, mul_comm (N.c α), div_eq_mul_inv]
  simp only [Pi.smul_apply, smul_eq_mul, NumD.vth, Units.val_mul]
  ring

/- English proof (translation)
Establish `rw₀ : GRep D.P.L (TF (R` using `R) F) (fun _ _ h => h (1 : TF (R := R) F ⟶ D.P.A).left ^ (m ^ 2) * (h p.g.b.left ^ (m ^ 2))⁻¹) (fun _ r z J => val w r.left z J) := ⟨_, inferInstance, _, _, w, hw, fun U _ h => prod_line _ _ h, fun _ _ _ _ _ => rfl⟩`. Take `⟨w', hw', v⟩` from `(rw₀.mul (grep_kap κ hκ p.g.b)).out D.P.isLB (DegPre.lineφ D F b) (DegPre.lineε 1) (fun U _ h => by`. Rewrite using `[prod_line, hb]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]`.

Use the proof step `module)`. Use `⟨w', hw', fun z J hJ => Eq.trans ?_ (v _ (𝟙 _) z J hJ).symm⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[Category.id_comp]`. Both sides reduce to the same expression.
-/
theorem exists_frame {m : ℕ} (p : QkPt D F (m ^ 2)) {w : Frm D F (m ^ 2) p.g.b} (hw : w.IsGen) {b : TF (R := R) F ⟶ D.P.A}
    (hb : b = p.g.b ^ m) {κ : LB.Gen (kapLB D (𝟙 D.P.A ^ m) (m ^ 2) 1)} (hκ : κ.IsGen) :
    ∃ w' : Frm D F 1 b, w'.IsGen ∧
      ∀ z J, Good D.P.L z J → val w (𝟙 _) z J * val κ p.g.b.left z J = val w' (𝟙 _) z J := by
  have rw₀ : GRep D.P.L (TF (R := R) F) (fun _ _ h => h (1 : TF (R := R) F ⟶ D.P.A).left ^ (m ^ 2) * (h p.g.b.left ^ (m ^ 2))⁻¹)
      (fun _ r z J => val w r.left z J) :=
    ⟨_, inferInstance, _, _, w, hw, fun U _ h => prod_line _ _ h, fun _ _ _ _ _ => rfl⟩
  obtain ⟨w', hw', v⟩ := (rw₀.mul (grep_kap κ hκ p.g.b)).out D.P.isLB (DegPre.lineφ D F b) (DegPre.lineε 1)
    (fun U _ h => by
      rw [prod_line, hb]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
  refine ⟨w', hw', fun z J hJ => Eq.trans ?_ (v _ (𝟙 _) z J hJ).symm⟩
  beta_reduce
  rw [Category.id_comp]
  rfl

end Values

section Theta

variable {S : Scheme.{0}} {T : Over S}

/- English proof (translation)
Establish `hy` using `hJ.mem (fun _ : Fin 1 => x.left) (𝟙 _)`. Rewrite using `[← Category.id_comp (ptSecT A x).left, sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (𝟙 _ ≫ (ptSecT A x).left) z J (fun _ => J (𝟙 _ ≫ x.left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd])]`. Use `Eq.trans ?_ ((congrArg (gs (𝟙 _) z _) (H _)).trans ((gs_mul _ z _ hy _ _).trans (congrArg₂ (· * ·) (gs_res _ z _ hy _) (gs_unit _ z _ hy _))))` and prove the remaining obligations. Conclude with `((gs_res _ z _ hy _).trans (gs_pull (𝟙 _) (ptSecT A x).left z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (𝟙 _ ≫ x.left))) (val_le A L x _ hy) _)).symm`.
-/
theorem sval_valueAt {A : Over S} [GrpObj A] {L : LB A.left} {a : ℤ} {s : LB.Sec (LPow A L a T)} {x : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s x τ v) {z : T.left} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (ptSecT A x).left z J =
      gs (𝟙 _) z ⊤ v * (val τ (𝟙 _) z J).val := by
  have hy := hJ.mem (fun _ : Fin 1 => x.left) (𝟙 _)
  rw [← Category.id_comp (ptSecT A x).left,
    sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (𝟙 _ ≫ (ptSecT A x).left) z J
    (fun _ => J (𝟙 _ ≫ x.left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd])]
  refine Eq.trans ?_ ((congrArg (gs (𝟙 _) z _) (H _)).trans ((gs_mul _ z _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_res _ z _ hy _) (gs_unit _ z _ hy _))))
  exact ((gs_res _ z _ hy _).trans (gs_pull (𝟙 _) (ptSecT A x).left z
    (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (𝟙 _ ≫ x.left))) (val_le A L x _ hy) _)).symm

/- English proof (translation)
Substitute `ha` using the available equality. Use `⟨ho, hu, fun p => ⟨⊤, trivial, ?_⟩⟩` and prove the remaining obligations. Take `⟨h, hh⟩` from `GlobalLift.exists_section (T := T) (V := ⊤) (p := p) trivial`. Establish `hi : overResι (T` using `T) ⊤ ≫ h = 𝟙 _ := by haveI : Mono (overResι (T := T) ⊤) := Over.mono_of_mono_left _ (hk := inferInstanceAs (Mono (⊤ : T.left.Opens).ι))`. Rewrite using `[← cancel_mono (overResι (T := T) ⊤), Category.assoc, hh, Category.comp_id, Category.id_comp]`.

Conclude with `ThetaCoord.isThetaPtOver_pull P ⟨th, s₁, α, τ, U, s₂, w, u, H⟩ _ h hi`.
-/
theorem isThetaPt_of_data (P : PolAV S) [Subsingleton T.left] {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)}
    {v : I → Γ(T.left, ⊤)} (ho : Odd k) (hu : IsUnit (k : Γ(T.left, ⊤))) {a : ℤ} (ha : a = (k : ℤ) ^ 2)
    (th : LB.Sec (LPow P.A P.L 1 T)) (s₁ : LB.Sec (LPow P.A P.L a T))
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ k).left] ![a, -1]))
    (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left) (fun _ => a)))
    (U : I → ThetaGrp P.A P.L a T) (s₂ : I → LB.Sec (LPow P.A P.L a T)) (w : I → Γ(T.left, ⊤)) (u : Γ(T.left, ⊤)ˣ)
    (H : IsGenSec P.A P.L 1 th ∧ α.IsGen ∧ τ.IsGen ∧
      IsTwistPull P.A P.L (mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _) a 1 α th s₁ ∧
      (∀ i, SymLift P.A P.L a (k ^ 2) (x i) (U i)) ∧ (∀ i, IsActOf P.A P.L a (U i) s₁ (s₂ i)) ∧
      (∀ i, IsValueAt P.A P.L a (s₂ i) 1 τ (w i)) ∧ ∀ i, v i = (u : Γ(T.left, ⊤)) * w i) :
    IsThetaPt P k x v := by
  subst ha
  refine ⟨ho, hu, fun p => ⟨⊤, trivial, ?_⟩⟩
  obtain ⟨h, hh⟩ := GlobalLift.exists_section (T := T) (V := ⊤) (p := p) trivial
  have hi : overResι (T := T) ⊤ ≫ h = 𝟙 _ := by
    haveI : Mono (overResι (T := T) ⊤) := Over.mono_of_mono_left _ (hk := inferInstanceAs (Mono (⊤ : T.left.Opens).ι))
    rw [← cancel_mono (overResι (T := T) ⊤), Category.assoc, hh, Category.comp_id, Category.id_comp]
  exact ThetaCoord.isThetaPtOver_pull P ⟨th, s₁, α, τ, U, s₂, w, u, H⟩ _ h hi

/- English proof (translation)
Establish `: Subsingleton (TFK (R` using `R) F).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))`. Take `⟨⟨_, _⟩, α, s₁, _, hα, hn, hs₁, -⟩` from `(existsUnique_thetaConst hL R A F ρ hρ m hm th 1 (one_pow _)).exists`. Establish `hU : ∀ i, ∃ θ, SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (x i) θ` using `fun i => by`. Take `⟨⟨_, _⟩, _, _, θ, -, -, -, hθ, -⟩` from `(existsUnique_thetaConst hL R A F ρ hρ m hm th (x i) (hx i)).exists`. Conclude with `⟨θ, hθ⟩`.

Use `choose U hU using hU`. Use `choose s₂ hs₂ using fun i => ThetaPtExist.exists_isTwistPull A.isLB (translT A.A (U i).pt) (translPt A.A (U i).pt) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) (U i).φ (U i).isGen s₁`. Establish `hτ` using `NormTheta.rigT_isGen (T := TFK (R := R) F) hρ ((m ^ 2 : ℕ) : ℤ)`. Use `choose w hw using fun i => ThetaPtExist.exists_isValueAt A.isLB (s₂ i) 1 (rigT A.A A.L ρ (TFK (R := R) F) ((m ^ 2 : ℕ) : ℤ)) hτ`. Establish `un : ∀ a : F, a ≠ 0 → IsUnit (fnOf a)` using `fun a ha => (IsUnit.mk0 _ ha).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom`.

Establish `hmu : IsUnit (m : Γ((TFK (R` using `R) F).left, ⊤)) := by`. Use `un m (Nat.cast_ne_zero.2 hm.pos.ne')` as an intermediate fact. Rewrite `this` using `[fnOf, map_natCast]`. Then use the resulting hypothesis. Use `isThetaPt_of_data A hm hmu (Nat.cast_pow m 2) th s₁ α _ U s₂ w (un u hu).unit ⟨hth, hα, hτ, hs₁, hU, hs₂, hw, fun i => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 (w i)`.

Establish `hc' : fnOf c = w i` using `hc`. Rewrite using `[hv i (s₂ i) c ⟨α, s₁, U i, hα, hn, hs₁, hU i, hs₂ i, fun z J hJ => by`. Use `sval_valueAt (hw i) hJ` as an intermediate fact. Rewrite `this` using `[← hc']`. Conclude with `this⟩, ← hc']`.

Conclude with `map_mul _ u c`.
-/
theorem isThetaPt_of_thC (hL : LL) {R : Type} [CommRing R] [IsDomain R] [CharZero R]
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) {F : Type} [Field F] [CharZero F] [Algebra (FractionRing R) F]
    {ρ : LB.Gen (A.L.pull (eSec A.A))} (hρ : ρ.IsGen) {m : ℕ} (hm : Odd m) {th : SecA A F 1}
    (hth : IsGenSec A.A A.L 1 th) {Ix : Type} {x : Ix → (TFK (R := R) F ⟶ A.A)} (hx : ∀ i, x i ^ (m ^ 2) = 1)
    {v : Ix → F} {u : F} (hu : u ≠ 0) (hv : ∀ i t c, ThC A ρ m th (x i) t c → v i = u * c) :
    IsThetaPt A m x fun i => fnOf (v i) := by
  have : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain ⟨⟨_, _⟩, α, s₁, _, hα, hn, hs₁, -⟩ :=
    (existsUnique_thetaConst hL R A F ρ hρ m hm th 1 (one_pow _)).exists
  have hU : ∀ i, ∃ θ, SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (x i) θ := fun i => by
    obtain ⟨⟨_, _⟩, _, _, θ, -, -, -, hθ, -⟩ := (existsUnique_thetaConst hL R A F ρ hρ m hm th (x i) (hx i)).exists
    exact ⟨θ, hθ⟩
  choose U hU using hU
  choose s₂ hs₂ using fun i => ThetaPtExist.exists_isTwistPull A.isLB (translT A.A (U i).pt) (translPt A.A (U i).pt)
    (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) (U i).φ (U i).isGen s₁
  have hτ := NormTheta.rigT_isGen (T := TFK (R := R) F) hρ ((m ^ 2 : ℕ) : ℤ)
  choose w hw using fun i => ThetaPtExist.exists_isValueAt A.isLB (s₂ i) 1
    (rigT A.A A.L ρ (TFK (R := R) F) ((m ^ 2 : ℕ) : ℤ)) hτ
  have un : ∀ a : F, a ≠ 0 → IsUnit (fnOf a) := fun a ha =>
    (IsUnit.mk0 _ ha).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  have hmu : IsUnit (m : Γ((TFK (R := R) F).left, ⊤)) := by
    have := un m (Nat.cast_ne_zero.2 hm.pos.ne')
    rwa [fnOf, map_natCast] at this
  refine isThetaPt_of_data A hm hmu (Nat.cast_pow m 2) th s₁ α _ U s₂ w (un u hu).unit
    ⟨hth, hα, hτ, hs₁, hU, hs₂, hw, fun i => ?_⟩
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 (w i)
  have hc' : fnOf c = w i := hc
  rw [hv i (s₂ i) c ⟨α, s₁, U i, hα, hn, hs₁, hU i, hs₂ i, fun z J hJ => by
    have := sval_valueAt (hw i) hJ
    rw [← hc'] at this
    exact this⟩, ← hc']
  exact map_mul _ u c

end Theta

/- English proof (translation)
Introduce and unpack `⟨hL, -⟩ hGt hFam R _ _ _ I ⟨hd, hc, h0⟩ rfl D A G _ _ hG U C _ _ _ _ _ _ hC N ν m hm Ix p q x hx hq`. Establish `hI : AdmBase R (IsLocalRing.maximalIdeal R)` using `⟨inferInstance, inferInstance, inferInstance, hc⟩`. Take `⟨g₁, g₂, g₃, -⟩` from `hGt R D.toPre D.psi_even D.tau_bimult C N ν`. Take `⟨f₁, f₂, -, ⟨ϑ, f, hf, hf0⟩, f₅, -⟩` from `hFam R D.toPre D.psi_even D.tau_bimult C N ν 1 le_rfl`. Take `⟨c, rfl⟩` from `f₅ ϑ f hf`.

Establish `hc0 : c ≠ 0` using `by rintro rfl; exact hf0 (zero_smul _ _)`. Take `⟨⟨ρ, hρ⟩, hw₀, -⟩` from `EvalZero.value_at_origin hL R _ hI D A G hG U C`. Take `⟨w₀, hN⟩` from `hw₀ ρ hρ`. Take `⟨e, he⟩` from `exists_linearEquiv_expandsF hL.1.globalFns U C (k := 1) le_rfl w₀ hN.1`. Establish `hth : IsGenSec A.A A.L 1 (e.symm ϑ)` using `fun t => by`.

Take `⟨f', hf', -⟩` from `f₁ (e t)`. Take `⟨c', rfl⟩` from `f₅ _ f' hf'`. Establish `h` using `famV_smul ν hf (c' / c)`. Rewrite `h` using `[smul_smul, div_mul_cancel₀ _ hc0]`. Establish `ht : t = ((c' / c) • e.symm ϑ : FieldBaseChange.SecOver (FieldBaseChange.abelianBase A C) _)` using `e.injective ((f₂ _ _ _ hf' h).trans (by rw [map_smul, e.apply_symm_apply]))`.

Use `⟨(Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c' / c), fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[ht]`. Both sides reduce to the same expression. Use `isThetaPt_of_thC hL A hρ hm hth (fun i => (hx i w₀ hN.1).1) (inv_ne_zero hc0) fun i t c' hc' => ?_` and prove the remaining obligations. Use `choose gs hgs hun using g₂`.

Take `⟨o, ho⟩` from `exists_zero_gt (D := D.toPre) (F := C)`. Take `⟨c₀, hc₀, -⟩` from `g₁ o`. Take `rfl : c₀ = 1` from `mul_eq_left.1 ((g₃ o o o _ _ _ hc₀ hc₀ hc₀).1 (ThetaSum.zero_isAdd ho o)).symm`. Establish `hns : GtPtF.IsNsmul m (p i).g (gs ((q i).1.2 ^ m))` using `⟨fun j => gs ((q i).1.2 ^ (j : ℕ)), by show (gs ((q i).1.2 ^ 0)).IsZero`. Rewrite using `[pow_zero, ← hun 1 o hc₀]`.

Conclude with `ho,`. Use `fun j => (g₃ _ _ _ _ _ _ (hgs _) (hq i).2 (hgs _)).2 (pow_succ _ _), rfl⟩`. Take `⟨⟨w, hw⟩, -⟩` from `SymFrame.main hL R _ hI D C (m ^ 2) hm.pow (p i)`. Take `⟨κ, hκ⟩` from `exists_kap (D := D.toPre) hL.1.mulPull m`. Take `⟨w', hw', hv⟩` from `exists_frame (p i) hw.1 (b := (gs ((q i).1.2 ^ m)).b) (by rw [← (hgs _).1, ← (hq i).2.1, NumD.Gt.pow_b, map_pow]) hκ.1`.

Establish `hs` using `hasSum_of_sumF hC (ThetaSum.theta_const_sum hL R _ hI D A G hG U C w₀ ρ hN (e.symm ϑ) ϑ ((he _ _).2 (e.apply_symm_apply ϑ)) m hm (p i) (x i) t c' (hx i) hc' w hw _ hns κ hκ w' hw' hv).1`. Establish `hs'` using `((ν.eX.toEquiv.hasSum_iff).2 hs).mul_left c⁻¹`. Use `HasSum.tsum_eq (hs'.congr_fun ?_)` and prove the remaining obligations. Introduce `α`. Conclude with `((congrArg (c⁻¹ * ·) (coef_eq_txT ν hL.1 hm (hq i) hw (hgs _) hκ hw' hv hf α)).trans (inv_mul_cancel_left₀ hc0 _)).symm`.
-/
theorem theta_const_eq_series : HV → BrGtSt → BrFamSt → TXSt := by
  rintro ⟨hL, -⟩ hGt hFam R _ _ _ I ⟨hd, hc, h0⟩ rfl D A G _ _ hG U C _ _ _ _ _ _ hC N ν m hm Ix p q x hx hq
  have hI : AdmBase R (IsLocalRing.maximalIdeal R) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨g₁, g₂, g₃, -⟩ := hGt R D.toPre D.psi_even D.tau_bimult C N ν
  obtain ⟨f₁, f₂, -, ⟨ϑ, f, hf, hf0⟩, f₅, -⟩ := hFam R D.toPre D.psi_even D.tau_bimult C N ν 1 le_rfl
  obtain ⟨c, rfl⟩ := f₅ ϑ f hf
  have hc0 : c ≠ 0 := by rintro rfl; exact hf0 (zero_smul _ _)
  obtain ⟨⟨ρ, hρ⟩, hw₀, -⟩ := EvalZero.value_at_origin hL R _ hI D A G hG U C
  obtain ⟨w₀, hN⟩ := hw₀ ρ hρ
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hL.1.globalFns U C (k := 1) le_rfl w₀ hN.1
  have hth : IsGenSec A.A A.L 1 (e.symm ϑ) := fun t => by
    obtain ⟨f', hf', -⟩ := f₁ (e t)
    obtain ⟨c', rfl⟩ := f₅ _ f' hf'
    have h := famV_smul ν hf (c' / c)
    rw [smul_smul, div_mul_cancel₀ _ hc0] at h
    have ht : t = ((c' / c) • e.symm ϑ : FieldBaseChange.SecOver (FieldBaseChange.abelianBase A C) _) :=
      e.injective ((f₂ _ _ _ hf' h).trans (by rw [map_smul, e.apply_symm_apply]))
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c' / c), fun j => ?_⟩
    rw [ht]
    rfl
  refine isThetaPt_of_thC hL A hρ hm hth (fun i => (hx i w₀ hN.1).1) (inv_ne_zero hc0) fun i t c' hc' => ?_
  choose gs hgs hun using g₂
  obtain ⟨o, ho⟩ := exists_zero_gt (D := D.toPre) (F := C)
  obtain ⟨c₀, hc₀, -⟩ := g₁ o
  obtain rfl : c₀ = 1 := mul_eq_left.1 ((g₃ o o o _ _ _ hc₀ hc₀ hc₀).1 (ThetaSum.zero_isAdd ho o)).symm
  have hns : GtPtF.IsNsmul m (p i).g (gs ((q i).1.2 ^ m)) :=
    ⟨fun j => gs ((q i).1.2 ^ (j : ℕ)), by
      show (gs ((q i).1.2 ^ 0)).IsZero
      rw [pow_zero, ← hun 1 o hc₀]; exact ho,
     fun j => (g₃ _ _ _ _ _ _ (hgs _) (hq i).2 (hgs _)).2 (pow_succ _ _), rfl⟩
  obtain ⟨⟨w, hw⟩, -⟩ := SymFrame.main hL R _ hI D C (m ^ 2) hm.pow (p i)
  obtain ⟨κ, hκ⟩ := exists_kap (D := D.toPre) hL.1.mulPull m
  obtain ⟨w', hw', hv⟩ := exists_frame (p i) hw.1 (b := (gs ((q i).1.2 ^ m)).b)
    (by rw [← (hgs _).1, ← (hq i).2.1, NumD.Gt.pow_b, map_pow]) hκ.1
  have hs := hasSum_of_sumF hC (ThetaSum.theta_const_sum hL R _ hI D A G hG U C w₀ ρ hN (e.symm ϑ) ϑ
    ((he _ _).2 (e.apply_symm_apply ϑ)) m hm (p i) (x i) t c' (hx i) hc' w hw _ hns κ hκ w' hw' hv).1
  have hs' := ((ν.eX.toEquiv.hasSum_iff).2 hs).mul_left c⁻¹
  refine HasSum.tsum_eq (hs'.congr_fun ?_)
  intro α
  exact ((congrArg (c⁻¹ * ·) (coef_eq_txT ν hL.1 hm (hq i) hw (hgs _) hκ hw' hv hf α)).trans
    (inv_mul_cancel_left₀ hc0 _)).symm

end GlobalTheory.Ex.ThetaSeries

end
