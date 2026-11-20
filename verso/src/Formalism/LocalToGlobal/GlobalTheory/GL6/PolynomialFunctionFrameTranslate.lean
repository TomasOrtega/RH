import Formalism.LocalToGlobal.GlobalTheory.GL6.MetricDisjointSupportOrthogonal
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionFamilyOf
import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Forms NumberField Classical Formalism.UG IsDedekindDomain

section Gen

variable {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Simplify using `[Formalism.REAL.fockF]`. Unfold `Formalism.REAL.fockF`. Rewrite using `[MvPolynomial.support_smul_eq hc, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [MvPolynomial.coeff_smul, smul_eq_mul, star_mul', RCLike.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fock_form_smul_smul (c : ℂ) (f : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    Formalism.REAL.fockF (c • f) (c • f) = (c * starRingEnd ℂ c) * Formalism.REAL.fockF f f := by
  by_cases hc : c = 0
  · subst hc; simp [Formalism.REAL.fockF]
  · unfold Formalism.REAL.fockF
    rw [MvPolynomial.support_smul_eq hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [MvPolynomial.coeff_smul, smul_eq_mul, star_mul', RCLike.star_def]
    ring

/- English proof (translation)
Unfold `nfAll`. Rewrite using `[fock_form_smul_smul, mul_div_assoc]`.
-/
theorem norm_form_smul_smul (lam : ι → DomWeight n) (c : ℂ) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam (c • p) (c • p) = (c * starRingEnd ℂ c) * nfAll lam p p := by
  unfold nfAll
  rw [fock_form_smul_smul, mul_div_assoc]

/- English proof (translation)
Establish `h : (subP o).comp (subP N) = subP (fun τ => N τ * o τ)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [AlgHom.comp_apply, subP, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C, Matrix.mul_apply, Finset.mul_sum, MvPolynomial.algebraMap_eq, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `show ((subP o).comp (subP N)) Q = _`. Rewrite using `[h]`.
-/
theorem substitution_comp (o N : ι → Matrix (Fin n) (Fin n) ℂ) (Q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    subP o (subP N Q) = subP (fun τ => N τ * o τ) Q := by
  have h : (subP o).comp (subP N) = subP (fun τ => N τ * o τ) := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [AlgHom.comp_apply, subP, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      Matrix.mul_apply, Finset.mul_sum, MvPolynomial.algebraMap_eq, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  show ((subP o).comp (subP N)) Q = _
  rw [h]

variable {K : Type} [Field K]

def t2iSub (M : ι → Matrix (Fin n) (Fin n) K) :
    MvPolynomial (ι × Fin n × Fin n) K →ₐ[K] MvPolynomial (ι × Fin n × Fin n) K :=
  MvPolynomial.aeval fun x => ∑ a', MvPolynomial.C (M x.1 x.2.1 a') * MvPolynomial.X (x.1, a', x.2.2)

/- English proof (translation)
Establish `: (MvPolynomial.map φ).comp (t2iSub M).toRingHom = (subP (fun τ => (M τ).map φ)).toRingHom.comp (MvPolynomial.map φ)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[t2iSub, subP]`. Introduce `x`.

Simplify using `[t2iSub, subP, Matrix.map_apply]`. Conclude with `congrArg (fun h : MvPolynomial (ι × Fin n × Fin n) K →+* MvPolynomial (ι × Fin n × Fin n) ℂ => h P) this`.
-/
theorem substitution_polynomial_map (φ : K →+* ℂ) (M : ι → Matrix (Fin n) (Fin n) K) (P : MvPolynomial (ι × Fin n × Fin n) K) :
    MvPolynomial.map φ (t2iSub M P) = subP (fun τ => (M τ).map φ) (MvPolynomial.map φ P) := by
  have : (MvPolynomial.map φ).comp (t2iSub M).toRingHom =
      (subP (fun τ => (M τ).map φ)).toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [t2iSub, subP]
    · intro x
      simp [t2iSub, subP, Matrix.map_apply]
  exact congrArg (fun h : MvPolynomial (ι × Fin n × Fin n) K →+* MvPolynomial (ι × Fin n × Fin n) ℂ => h P) this

end Gen

section Transport

variable {D : D7} {u : D.what₂.Word}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨k, hk, δ, hδ⟩` from `diamond_elements_exist_all Tf 0 (Nat.zero_le _) v a`. Establish `hcl` using `(Tf.val 0 (Nat.zero_le _)).dil v a k hk c δ hδ`. Take `⟨hh, hhH, κ, hκK, e⟩` from `(DoubleCoset.eq _ _ _ _).1 hcl`. Establish `hκ : κ.1 ∈ (Tf.cls 0 (Nat.zero_le _)).lev.U` using `hκK`. Take `⟨g, hgU, hge⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)`.

Establish `hx : ((Tf.cls 0 (Nat.zero_le _)).y c * δ).1 = bc (inclE (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g * ((Tf.cls 0 (Nat.zero_le _)).y ((D.fm u).dil 0 v a c)).1 * κ.1 := by`. Rewrite using `[e]`. Simplify using `only [Subgroup.coe_mul]`. Rewrite using `[← hge]`. Take `⟨n, hn, hχ⟩` from `hC`.

Take `⟨hpow, r, hr⟩` from `hχ 0 (Nat.zero_le _) ⟨κ.1, hκ⟩`. Establish `hgi : g⁻¹ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))` using `(UJ _ _).inv_mem hgU`. Use `⟨g⁻¹, hgi, r, ⟨n, hn, by rw [hr]; exact hpow⟩, fun x z => ?_⟩` and prove the remaining obligations. Take `⟨gA, hgA, hgAφ⟩` from `forms_from_adelic_function Tf 0 (Nat.zero_le _) ((D.fm u).emb 0 x) (embedding_mem_forms x)`. Establish `hAd` using `(Submodule.mem_inf.1 hgA).1`.

Rewrite using `[t2sRv_spec, (D.fm u).rhoT_dil, hgAφ, (Tf.val 0 (Nat.zero_le _)).dilT v a k hk c δ hδ gA hAd]`. Use `beta_reduce`. Rewrite using `[adelic_value_translate (Tf.cls 0 (Nat.zero_le _)).lev (embT D) (fun τ x => embedding_conj_compat D τ x) hAd g hgU _ _ ⟨κ.1, hκ⟩ hx, hr, Equiv.apply_symm_apply]`.
-/
theorem diamond_value_root_of_unity (Tf : FormsTied D u) (hC : ChiFin Tf) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ)
    (c : (D.mem u).C.cls 0) :
    ∃ (γ : GL (Fin (D.R.N 0)) D.host.E) (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
      (r : D.what₂.LL), (∃ n : ℕ, 0 < n ∧ D.what₂.embLL r ^ n = 1) ∧
      ∀ (x : ((D.fm u).lat 0).V) z, (D.fm u).emb 0 (t2sRv v a x) c z =
        D.what₂.embLL r * (D.fm u).emb 0 x ((D.fm u).dil 0 v a c)
          ((Tf.val 0 (Nat.zero_le _)).eY.symm
            (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ hγ ((Tf.val 0 (Nat.zero_le _)).eY z))) := by
  obtain ⟨k, hk, δ, hδ⟩ := diamond_elements_exist_all Tf 0 (Nat.zero_le _) v a
  have hcl := (Tf.val 0 (Nat.zero_le _)).dil v a k hk c δ hδ
  obtain ⟨hh, hhH, κ, hκK, e⟩ := (DoubleCoset.eq _ _ _ _).1 hcl
  have hκ : κ.1 ∈ (Tf.cls 0 (Nat.zero_le _)).lev.U := hκK
  obtain ⟨g, hgU, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
  have hx : ((Tf.cls 0 (Nat.zero_le _)).y c * δ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g *
        ((Tf.cls 0 (Nat.zero_le _)).y ((D.fm u).dil 0 v a c)).1 * κ.1 := by
    rw [e]
    simp only [Subgroup.coe_mul]
    rw [← hge]
  obtain ⟨n, hn, hχ⟩ := hC
  obtain ⟨hpow, r, hr⟩ := hχ 0 (Nat.zero_le _) ⟨κ.1, hκ⟩
  have hgi : g⁻¹ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) := (UJ _ _).inv_mem hgU
  refine ⟨g⁻¹, hgi, r, ⟨n, hn, by rw [hr]; exact hpow⟩, fun x z => ?_⟩
  obtain ⟨gA, hgA, hgAφ⟩ := forms_from_adelic_function Tf 0 (Nat.zero_le _) ((D.fm u).emb 0 x) (embedding_mem_forms x)
  have hAd := (Submodule.mem_inf.1 hgA).1
  rw [t2sRv_spec, (D.fm u).rhoT_dil, hgAφ, (Tf.val 0 (Nat.zero_le _)).dilT v a k hk c δ hδ gA hAd]
  beta_reduce
  rw [adelic_value_translate (Tf.cls 0 (Nat.zero_le _)).lev (embT D) (fun τ x => embedding_conj_compat D τ x) hAd g hgU _ _
    ⟨κ.1, hκ⟩ hx, hr, Equiv.apply_symm_apply]

end Transport

section Reps

variable {D : D7} {u : D.what₂.Word}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def t2iM (γ : GL (Fin (D.R.N 0)) D.host.E) : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL :=
  fun τ => (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map
    (D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E))

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[t2iM, atInf, embS]`.
-/
theorem at_infinity_matrix_map (γ : GL (Fin (D.R.N 0)) D.host.E) (s : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) :
    (t2iM γ τ).map s = atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ := by
  ext i j
  simp [t2iM, atInf, embS]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[t2iM, atInf, bwA_embT_eq]`.
-/
theorem at_infinity_matrix_embedding (γ : GL (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) :
    (t2iM γ τ).map D.what₂.embLL = atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ := by
  ext i j
  simp [t2iM, atInf, bwA_embT_eq]

def t2iP (γ : GL (Fin (D.R.N 0)) D.host.E) (r : D.what₂.LL)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL) :
    MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL :=
  MvPolynomial.C (r * ∏ τ, (t2iM γ τ).det ^ shiftOf (lamT u 0) τ) * t2iSub (t2iM γ) P

/- English proof (translation)
Simplify using `only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, frameTranslate, Pi.one_apply, Matrix.one_mul]`.
-/
theorem polynomial_function_frame_translate (γ : GL (Fin (D.R.N 0)) D.host.E)
    (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ) (y : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embT D))) :
    fnOf _ (shiftOf (lamT u 0)) 1 P (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ hγ y) =
      fnOf _ (shiftOf (lamT u 0)) (atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)) P y := by
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, frameTranslate, Pi.one_apply, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[polynomial_function_frame_translate]`. Establish `h1` using `fnOf_mul (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0)) (atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)) 1 (MvPolynomial.map D.what₂.embLL P)`. Simplify using `only [Pi.one_apply, Matrix.mul_one] at h1`. Establish `h3 : (fun τ => (t2iM γ τ).map D.what₂.embLL) = atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)`. Use function extensionality and compare the values at `fun τ => at_infinity_matrix_embedding γ τ`.

Establish `h4 : ∀ τ, D.what₂.embLL ((t2iM γ τ).det ^ shiftOf (lamT u 0) τ) = (atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det ^ shiftOf (lamT u 0) τ`. Introduce `τ`. Rewrite using `[map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply, at_infinity_matrix_embedding]`. Establish `hmap : MvPolynomial.map D.what₂.embLL (t2iP (u` using `u) γ r P) = (D.what₂.embLL r * ∏ τ, (atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det ^ shiftOf (lamT u 0) τ) • subP (atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)) (MvPolynomial.map D.what₂.embLL P) := by`. Rewrite using `[t2iP, (MvPolynomial.map D.what₂.embLL).map_mul, MvPolynomial.map_C, substitution_polynomial_map, h3, MvPolynomial.smul_eq_C_mul, D.what₂.embLL.map_mul, map_prod]`.

Simplify using `only [h4]`. Use `erw [h1]`. Rewrite using `[← MvPolynomial.smul_eq_C_mul, map_smul, Pi.smul_apply, smul_eq_mul, hmap, map_smul, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem polynomial_rep_translate_rho (γ : GL (Fin (D.R.N 0)) D.host.E)
    (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (r : D.what₂.LL)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL)
    (y : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embT D))) :
    D.what₂.embLL r * fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL P)
        (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ hγ y) =
      fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL (t2iP (u := u) γ r P)) y := by
  rw [polynomial_function_frame_translate]
  have h1 := fnOf_mul (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0))
    (atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)) 1 (MvPolynomial.map D.what₂.embLL P)
  simp only [Pi.one_apply, Matrix.mul_one] at h1
  have h3 : (fun τ => (t2iM γ τ).map D.what₂.embLL) = atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) :=
    funext fun τ => at_infinity_matrix_embedding γ τ
  have h4 : ∀ τ, D.what₂.embLL ((t2iM γ τ).det ^ shiftOf (lamT u 0) τ) =
      (atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det ^ shiftOf (lamT u 0) τ := by
    intro τ
    rw [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply, at_infinity_matrix_embedding]
  have hmap : MvPolynomial.map D.what₂.embLL (t2iP (u := u) γ r P) =
      (D.what₂.embLL r * ∏ τ, (atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det ^
        shiftOf (lamT u 0) τ) • subP (atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E))
          (MvPolynomial.map D.what₂.embLL P) := by
    rw [t2iP, (MvPolynomial.map D.what₂.embLL).map_mul, MvPolynomial.map_C, substitution_polynomial_map, h3,
      MvPolynomial.smul_eq_C_mul, D.what₂.embLL.map_mul, map_prod]
    simp only [h4]
  erw [h1]
  rw [← MvPolynomial.smul_eq_C_mul, map_smul, Pi.smul_apply, smul_eq_mul, hmap, map_smul, Pi.smul_apply, smul_eq_mul]
  ring

end Reps

section Norms

variable {D : D7} {u : D.what₂.Word}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Rewrite using `[t2iP, (MvPolynomial.map φ).map_mul, MvPolynomial.map_C, substitution_polynomial_map, MvPolynomial.smul_eq_C_mul, φ.map_mul, map_prod]`. Simplify using `only [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]`.
-/
theorem polynomial_translate_map (φ : D.what₂.LL →+* ℂ) (γ : GL (Fin (D.R.N 0)) D.host.E) (r : D.what₂.LL)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL) :
    MvPolynomial.map φ (t2iP (u := u) γ r P) =
      (φ r * ∏ τ, ((t2iM γ τ).map φ).det ^ shiftOf (lamT u 0) τ) •
        subP (fun τ => (t2iM γ τ).map φ) (MvPolynomial.map φ P) := by
  rw [t2iP, (MvPolynomial.map φ).map_mul, MvPolynomial.map_C, substitution_polynomial_map, MvPolynomial.smul_eq_C_mul, φ.map_mul,
    map_prod]
  simp only [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]

def t2iT (s : D.what₂.LL →+* ℂ) (o : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D s))) (c : (D.mem u).C.cls 0)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL) : ℝ :=
  ((D.mem u).C.wt 0 c).re * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u 0) τ)) *
    (nfAll ((D.fm u).lam 0) (subP o.1 (MvPolynomial.map s P)) (subP o.1 (MvPolynomial.map s P))).re

/- English proof (translation)
Take `⟨n, hn, h⟩` from `hr`. Establish `h1 : r ^ n = 1` using `D.what₂.embLL.injective (by rw [map_pow, h, map_one])`. Establish `h2 : s r ^ n = 1` using `by rw [← map_pow, h1, map_one]`. Establish `h3 : ‖s r‖ = 1`. Establish `h4` using `congrArg norm h2`.

Rewrite `h4` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h4`. Rewrite using `[Complex.normSq_eq_norm_sq, h3, one_pow]`.
-/
theorem normSq_root_of_unity_eq_one (r : D.what₂.LL) (hr : ∃ n : ℕ, 0 < n ∧ D.what₂.embLL r ^ n = 1) (s : D.what₂.LL →+* ℂ) :
    Complex.normSq (s r) = 1 := by
  obtain ⟨n, hn, h⟩ := hr
  have h1 : r ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, h, map_one])
  have h2 : s r ^ n = 1 := by rw [← map_pow, h1, map_one]
  have h3 : ‖s r‖ = 1 := by
    have h4 := congrArg norm h2
    rw [norm_pow, norm_one] at h4
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h4
  rw [Complex.normSq_eq_norm_sq, h3, one_pow]

/- English proof (translation)
Unfold `t2iT`. Rewrite using `[polynomial_translate_map]`. Establish `hM : (fun τ => (t2iM γ τ).map s) = atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)`. Use function extensionality and compare the values at `fun τ => at_infinity_matrix_map γ s τ`. Simplify using `only [at_infinity_matrix_map]`.

Use `set μ : ℂ := s r * ∏ τ, (atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det ^ shiftOf (lamT u 0) τ with hμ`. Rewrite using `[map_smul, substitution_comp, norm_form_smul_smul, Complex.mul_conj, Complex.re_ofReal_mul]`. Establish `hμn : Complex.normSq μ = ∏ τ, ‖(atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det‖ ^ (2 * shiftOf (lamT u 0) τ)`. Rewrite using `[hμ, map_mul, normSq_root_of_unity_eq_one r hr s, one_mul, map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[map_zpow₀, Complex.normSq_eq_norm_sq, zpow_mul]`. Use `norm_cast`. Establish `hdet : ∀ τ, ((frameTranslate (embS D s) (fun τ x => D.sp.cm.cmUnram.2.1 (embS D s τ) x) γ hγ o).1 τ).det = (atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det * (o.1 τ).det` using `fun τ => Matrix.det_mul _ _`. Simplify using `only [hdet, norm_mul, mul_zpow, Finset.prod_mul_distrib, hμn]`. Use `show _ = ((D.mem u).C.wt 0 c).re * ((∏ τ, ‖(atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det‖ ^ (2 * shiftOf (lamT u 0) τ)) * ∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u 0) τ)) * (nfAll ((D.fm u).lam 0) (subP (fun τ => atInf (embS D s) (γ : Matrix (Fin …`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem residue_eval_translate_rho (γ : GL (Fin (D.R.N 0)) D.host.E)
    (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (r : D.what₂.LL)
    (hr : ∃ n : ℕ, 0 < n ∧ D.what₂.embLL r ^ n = 1)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL) (s : D.what₂.LL →+* ℂ)
    (o : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D s))) (c : (D.mem u).C.cls 0) :
    t2iT s o c (t2iP (u := u) γ r P) =
      t2iT s (frameTranslate (embS D s) (fun τ x => D.sp.cm.cmUnram.2.1 (embS D s τ) x) γ hγ o) c P := by
  unfold t2iT
  rw [polynomial_translate_map]
  have hM : (fun τ => (t2iM γ τ).map s) = atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) :=
    funext fun τ => at_infinity_matrix_map γ s τ
  simp only [at_infinity_matrix_map]
  set μ : ℂ := s r * ∏ τ, (atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det ^
    shiftOf (lamT u 0) τ with hμ
  rw [map_smul, substitution_comp, norm_form_smul_smul, Complex.mul_conj, Complex.re_ofReal_mul]
  have hμn : Complex.normSq μ = ∏ τ, ‖(atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det‖ ^
      (2 * shiftOf (lamT u 0) τ) := by
    rw [hμ, map_mul, normSq_root_of_unity_eq_one r hr s, one_mul, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, Complex.normSq_eq_norm_sq, zpow_mul]
    norm_cast
  have hdet : ∀ τ, ((frameTranslate (embS D s) (fun τ x => D.sp.cm.cmUnram.2.1 (embS D s τ) x) γ hγ o).1 τ).det =
      (atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det * (o.1 τ).det := fun τ =>
    Matrix.det_mul _ _
  simp only [hdet, norm_mul, mul_zpow, Finset.prod_mul_distrib, hμn]
  show _ = ((D.mem u).C.wt 0 c).re * ((∏ τ, ‖(atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det‖ ^
      (2 * shiftOf (lamT u 0) τ)) * ∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u 0) τ)) *
    (nfAll ((D.fm u).lam 0) (subP (fun τ => atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ * o.1 τ)
      (MvPolynomial.map s P)) (subP (fun τ => atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ * o.1 τ)
      (MvPolynomial.map s P))).re
  ring

end Norms

section Iso

variable {D : D7} {u : D.what₂.Word}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def t2iRes (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    ((D.fm u).lat 0).V :=
  (restriction_rational_form Tf hS x (fun c' => c' = c)).choose

/- English proof (translation)
The claim follows from `(restriction_rational_form Tf hS x (fun c' => c' = c)).choose_spec`.
-/
theorem t2iRes_spec (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    (D.fm u).emb 0 (t2iRes Tf hS x c) = fun c' => if c' = c then (D.fm u).emb 0 x c' else 0 :=
  (restriction_rational_form Tf hS x (fun c' => c' = c)).choose_spec

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Rewrite using `[Tf.norm 0 (Nat.zero_le _) s (t2iRes Tf hS x c) (fun c' => if c' = c then P else 0) ?_ o ho]`. Rewrite using `[Finset.sum_eq_single c]`. Simplify using `only [if_pos rfl]`. Both sides reduce to the same expression. Introduce `c' _ hc`.

Simplify using `only [hc, if_false, map_zero, norm_form_zero, Complex.zero_re, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ c) h`. Introduce `c' z`. Rewrite using `[t2iRes_spec]`.

Distinguish the cases in `h : c' = c`. Substitute `h` using the available equality. Simplify using `only [if_pos rfl]`. Conclude with `hP z`. Simplify using `only [h, if_false, map_zero, Pi.zero_apply]`.
-/
theorem polynomial_rep_residue_eval (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL)
    (hP : ∀ z, (D.fm u).emb 0 x c z = fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL P)
      ((Tf.val 0 (Nat.zero_le _)).eY z))
    (s : D.what₂.LL →+* ℂ) (o : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D s))) (ho : o.IsON) :
    (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X (InfinitePlace.mk s) (t2iRes Tf hS x c) (t2iRes Tf hS x c)).re =
      t2iT s o c P := by
  rw [Tf.norm 0 (Nat.zero_le _) s (t2iRes Tf hS x c) (fun c' => if c' = c then P else 0) ?_ o ho]
  · rw [Finset.sum_eq_single c]
    · simp only [if_pos rfl]; rfl
    · intro c' _ hc
      simp only [hc, if_false, map_zero, norm_form_zero, Complex.zero_re, mul_zero]
    · intro h; exact absurd (Finset.mem_univ c) h
  · intro c' z
    rw [t2iRes_spec]
    by_cases h : c' = c
    · subst h; simp only [if_pos rfl]; exact hP z
    · simp only [h, if_false, map_zero, Pi.zero_apply]

def t2iDil (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) : (D.mem u).C.cls 0 ≃ (D.mem u).C.cls 0 where
  toFun := (D.fm u).dil 0 v a
  invFun := (D.fm u).dil 0 v a⁻¹
  left_inv c := by rw [← (D.fm u).dil_mul, inv_mul_cancel, (D.fm u).dil_one]
  right_inv c := by rw [← (D.fm u).dil_mul, mul_inv_cancel, (D.fm u).dil_one]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨C, hC', -, -⟩` from `(Tf.val 0 (Nat.zero_le _)).de`. Take `⟨o, ho⟩` from `exists_isON_of_gram (sigD D : D.host.E →+* D.host.E) (embS D s) (fun τ x => D.sp.cm.cmUnram.2.1 (embS D s τ) x) (gramN D 0 (Nat.zero_le _)) C hC'`. Take `⟨Px, -, hPx⟩` from `polynomial_rep_of_rational_form Tf x`. Use `choose γ hγ r hr hval using fun c => diamond_value_root_of_unity Tf hC v a c`. Establish `hrep : ∀ c z, (D.fm u).emb 0 (t2sRv v a x) c z = fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL (t2iP (u` using `u) (γ c) (r c) (Px ((D.fm u).dil 0 v a c)))) ((Tf.val 0 (Nat.zero_le _)).eY z) := by`.

Introduce `c z`. Rewrite using `[hval c x z, hPx, Equiv.apply_symm_apply, polynomial_rep_translate_rho]`. Establish `hwt : ∀ c, (D.mem u).C.wt 0 c = 1` using `fun c => Formalism.BasicNotions.factWtZero _ _ _ (D.mem u).C hS c`. Rewrite using `[Tf.norm 0 (Nat.zero_le _) s _ _ hrep o ho, Tf.norm 0 (Nat.zero_le _) s x Px hPx o ho]`. Use `conv_rhs => rw [← Equiv.sum_comp (t2iDil v a)]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `e1` using `residue_eval_translate_rho (u := u) (γ c) (hγ c) (r c) (hr c) (Px ((D.fm u).dil 0 v a c)) s o c`. Establish `ho'` using `frame_translate_is_orthonormal (embS D s) (fun τ x => D.sp.cm.cmUnram.2.1 (embS D s τ) x) (γ c) (hγ c) o ho`. Establish `e2` using `polynomial_rep_residue_eval Tf hS x ((D.fm u).dil 0 v a c) (Px ((D.fm u).dil 0 v a c)) (hPx _) s _ ho'`. Establish `e3` using `polynomial_rep_residue_eval Tf hS x ((D.fm u).dil 0 v a c) (Px ((D.fm u).dil 0 v a c)) (hPx _) s o ho`.

Establish `e4 : ∀ (o' : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D s))) P, t2iT (u` using `u) s o' c P = t2iT s o' ((D.fm u).dil 0 v a c) P := by`. Introduce `o' P`. Unfold `t2iT`. Rewrite using `[hwt, hwt]`. Express the relevant statement in the definitionally equal form `t2iT s o c _ = t2iT s o ((D.fm u).dil 0 v a c) _`.

Rewrite using `[e1, e4, ← e2, e3]`. Both sides reduce to the same expression.
-/
theorem majorant_norm_diamond_invariant (Tf : FormsTied D u) (hC : ChiFin Tf) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (v : (D.mem u).A.vT)
    (a : ((D.mem u).A.Fv v)ˣ) (x : ((D.fm u).lat 0).V) (s : D.what₂.LL →+* ℂ) :
    (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X (InfinitePlace.mk s) (t2sRv v a x) (t2sRv v a x)).re =
      (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X (InfinitePlace.mk s) x x).re := by
  obtain ⟨C, hC', -, -⟩ := (Tf.val 0 (Nat.zero_le _)).de
  obtain ⟨o, ho⟩ := exists_isON_of_gram (sigD D : D.host.E →+* D.host.E) (embS D s)
    (fun τ x => D.sp.cm.cmUnram.2.1 (embS D s τ) x) (gramN D 0 (Nat.zero_le _)) C hC'
  obtain ⟨Px, -, hPx⟩ := polynomial_rep_of_rational_form Tf x
  choose γ hγ r hr hval using fun c => diamond_value_root_of_unity Tf hC v a c
  have hrep : ∀ c z, (D.fm u).emb 0 (t2sRv v a x) c z = fnOf _ (shiftOf (lamT u 0)) 1
      (MvPolynomial.map D.what₂.embLL (t2iP (u := u) (γ c) (r c) (Px ((D.fm u).dil 0 v a c))))
      ((Tf.val 0 (Nat.zero_le _)).eY z) := by
    intro c z
    rw [hval c x z, hPx, Equiv.apply_symm_apply, polynomial_rep_translate_rho]
  have hwt : ∀ c, (D.mem u).C.wt 0 c = 1 := fun c => Formalism.BasicNotions.factWtZero _ _ _ (D.mem u).C hS c
  rw [Tf.norm 0 (Nat.zero_le _) s _ _ hrep o ho, Tf.norm 0 (Nat.zero_le _) s x Px hPx o ho]
  conv_rhs => rw [← Equiv.sum_comp (t2iDil v a)]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 := residue_eval_translate_rho (u := u) (γ c) (hγ c) (r c) (hr c) (Px ((D.fm u).dil 0 v a c)) s o c
  have ho' := frame_translate_is_orthonormal (embS D s) (fun τ x => D.sp.cm.cmUnram.2.1 (embS D s τ) x) (γ c) (hγ c) o ho
  have e2 := polynomial_rep_residue_eval Tf hS x ((D.fm u).dil 0 v a c) (Px ((D.fm u).dil 0 v a c)) (hPx _) s _ ho'
  have e3 := polynomial_rep_residue_eval Tf hS x ((D.fm u).dil 0 v a c) (Px ((D.fm u).dil 0 v a c)) (hPx _) s o ho
  have e4 : ∀ (o' : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D s))) P,
      t2iT (u := u) s o' c P = t2iT s o' ((D.fm u).dil 0 v a c) P := by
    intro o' P; unfold t2iT; rw [hwt, hwt]
  change t2iT s o c _ = t2iT s o ((D.fm u).dil 0 v a c) _
  rw [e1, e4, ← e2, e3]
  rfl

/- English proof (translation)
Introduce `v w a x y`. Establish `hv : InfinitePlace.mk v.embedding = v` using `InfinitePlace.mk_embedding v`. Establish `hF` using `isSesq_comp (isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X) (t2sRv w a) v`. Establish `hG` using `isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v`. Use `sesq_ext (F := fun x y => majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (t2sRv w a x) (t2sRv w a y)) (G := majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v) (σ := v.embedding) (exists_im_ne_zero v) hF hG (fun z => ?_) x y` and prove the remaining obligations.

Use `show majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (t2sRv w a z) (t2sRv w a z) = majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v z z`. Establish `h` using `majorant_norm_diamond_invariant Tf hC hS w a z v.embedding`. Rewrite `h` using `[hv]`. Rewrite `h`, the goal using `[majAt_self, majAt_self]`. Rewrite `h` using `[Complex.ofReal_re, Complex.ofReal_re]`.

Rewrite using `[h]`.
-/
theorem diamond_isometry_at_infinity (Tf : FormsTied D u) (hC : ChiFin Tf) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) : DiamondIsometry D u := by
  intro v w a x y
  have hv : InfinitePlace.mk v.embedding = v := InfinitePlace.mk_embedding v
  have hF := isSesq_comp (isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X) (t2sRv w a) v
  have hG := isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v
  refine sesq_ext (F := fun x y => majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (t2sRv w a x) (t2sRv w a y))
    (G := majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v) (σ := v.embedding) (exists_im_ne_zero v) hF hG (fun z => ?_) x y
  show majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (t2sRv w a z) (t2sRv w a z) =
    majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v z z
  have h := majorant_norm_diamond_invariant Tf hC hS w a z v.embedding
  rw [hv] at h
  rw [majAt_self, majAt_self] at h ⊢
  rw [Complex.ofReal_re, Complex.ofReal_re] at h
  rw [h]

end Iso

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
