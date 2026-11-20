import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairLatticeLocalSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicVectorLatticeLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIwasawaMajorantFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicArchimedeanEigenvectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantStabilizerIwasawaLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantFrameCommutesCartanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhereStatement

noncomputable section

namespace GlobalTheory.IwLine
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

section Glue
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

open Classical in

/- English proof (translation)
Establish `key : ∀ s : Finset (InfinitePlace F), ∃ q : GAd σ J, (∀ v, proj σ J v q = 1) ∧ ∀ w, projArch σ J w q = if w ∈ s then x w else 1`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨1, fun v => map_one _, fun w => by simp⟩`. Consider the case `insert a s ha ih`.

Take `⟨q, h1, h2⟩` from `ih`. Use `⟨embArch σ J a (x a) * q, fun v => by simp [h1 v], fun u => ?_⟩` and prove the remaining obligations. Distinguish the cases in `e : u = a`. Substitute `e` using the available equality. Simplify using `[h2 u, ha]`.

Rewrite using `[map_mul, projArch_embArch_ne σ J e, one_mul, h2 u]`. Simplify using `[Finset.mem_insert, e]`. Take `⟨q, h1, h2⟩` from `key Finset.univ`. Conclude with `⟨q, h1, fun w => by rw [h2 w, if_pos (Finset.mem_univ w)]⟩`.
-/
theorem exists_arch_comp (x : ∀ w : InfinitePlace F, GArch σ J w) :
    ∃ q : GAd σ J, (∀ v, proj σ J v q = 1) ∧ ∀ w, projArch σ J w q = x w := by
  have key : ∀ s : Finset (InfinitePlace F), ∃ q : GAd σ J, (∀ v, proj σ J v q = 1) ∧
      ∀ w, projArch σ J w q = if w ∈ s then x w else 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, fun v => map_one _, fun w => by simp⟩
    | insert a s ha ih =>
      obtain ⟨q, h1, h2⟩ := ih
      refine ⟨embArch σ J a (x a) * q, fun v => by simp [h1 v], fun u => ?_⟩
      by_cases e : u = a
      · subst e; simp [h2 u, ha]
      · rw [map_mul, projArch_embArch_ne σ J e, one_mul, h2 u]; simp [Finset.mem_insert, e]
  obtain ⟨q, h1, h2⟩ := key Finset.univ
  exact ⟨q, h1, fun w => by rw [h2 w, if_pos (Finset.mem_univ w)]⟩

open Classical in

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨1, fun w => map_one _, fun v => by simp⟩`. Consider the case `insert a s ha ih`. Take `⟨q, h1, h2⟩` from `ih`. Use `⟨emb σ J a (x a) * q, fun w => by simp [h1 w], fun u => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `e : u = a`. Substitute `e` using the available equality. Simplify using `[h2 u, ha]`. Rewrite using `[map_mul, proj_emb_ne σ J e, one_mul, h2 u]`. Simplify using `[Finset.mem_insert, e]`.
-/
theorem exists_fin_comp (x : ∀ v : HeightOneSpectrum (𝓞 F), GLoc σ J v) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ q : GAd σ J, (∀ w, projArch σ J w q = 1) ∧ ∀ v, proj σ J v q = if v ∈ S then x v else 1 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun w => map_one _, fun v => by simp⟩
  | insert a s ha ih =>
    obtain ⟨q, h1, h2⟩ := ih
    refine ⟨emb σ J a (x a) * q, fun w => by simp [h1 w], fun u => ?_⟩
    by_cases e : u = a
    · subst e; simp [h2 u, ha]
    · rw [map_mul, proj_emb_ne σ J e, one_mul, h2 u]; simp [Finset.mem_insert, e]

end Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [cT, form, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, dotProduct, Matrix.mulVec, AlgHom.coe_toRingHom, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cT_col_eq_form {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => a i) * Jᵀ * (Matrix.of fun i (_ : Fin 1) => b i) =
      Matrix.of fun _ _ => form σ J b a := by
  ext i j
  simp only [cT, form, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, dotProduct,
    Matrix.mulVec, AlgHom.coe_toRingHom, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/- English proof (translation)
Take `⟨rfl, A, hA⟩` from `h`. Introduce `h0`. Set `A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ` to `A.submatrix id finSumFinEquiv.symm`. Establish `h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm`. Rewrite using `[← hA]`.

Use extensionality with `i j`. Simplify using `[A', Matrix.mul_apply]`. Establish `h2` using `congrArg Matrix.det h1`. Rewrite `h2` using `[Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg, Matrix.det_one]`. Simplify using `at h2`.

Conclude with `absurd h2.symm (by simp)`.
-/
theorem det_ne_zero_of_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  intro h0
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_neg, Matrix.det_one] at h2
  simp at h2
  exact absurd h2.symm (by simp)

/- English proof (translation)
Use `⟨fun i j => by simpa [Matrix.transpose_apply] using hX.herm j i, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_transpose]`. Introduce `h0`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Apply `det_ne_zero_of_sig (hX.sig w)` to reduce the goal to its premises.

Establish `e` using `RingHom.map_det ((B.emb w).1) X.J`. Rewrite `e` using `[h0, map_zero]`. Conclude with `e.symm`.
-/
theorem isHermND_transpose {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsHerm σ B r s) :
    IsHermND σ X.Jᵀ := by
  refine ⟨fun i j => by simpa [Matrix.transpose_apply] using hX.herm j i, ?_⟩
  rw [Matrix.det_transpose]
  intro h0
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  apply det_ne_zero_of_sig (hX.sig w)
  have e := RingHom.map_det ((B.emb w).1) X.J
  rw [h0, map_zero] at e
  exact e.symm

end GlobalTheory.IwLine

namespace GlobalTheory.IwLine
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use `haveI : X.L.IsLattice E := hX.lat`. Establish `hσ : IsCMExt F E σ` using `hB.cm`. Establish `hs : ∀ z : E, σ (σ z) = z` using `fun z => by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Conclude with `τ.injective (by rw [hσ.2.2.2, hσ.2.2.2, star_star])`.

Establish `hND : IsHermND σ X.Jᵀ` using `isHermND_transpose hX`. Use `set xc : Matrix (Fin n) (Fin 1) E := Matrix.of fun i _ => H.x i with hxc`. Use `set yc : Matrix (Fin n) (Fin 1) E := Matrix.of fun i _ => H.y i with hyc`. Establish `hfyx : form σ X.J H.y H.x = 1`. Establish `e : form σ X.J H.y H.x = σ (form σ X.J H.x H.y)`.

Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hs, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← hX.herm k l, hs]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, hH.xy, map_one]`. Establish `hxx : cT (σ : E →+* E) xc * X.Jᵀ * xc = 0`. Rewrite using `[cT_col_eq_form]`. Use extensionality with `i j`. Simplify using `[hH.xx]`.

Establish `hyy : cT (σ : E →+* E) yc * X.Jᵀ * yc = 0`. Rewrite using `[cT_col_eq_form]`. Use extensionality with `i j`. Simplify using `[hH.yy]`. Establish `hxy : cT (σ : E →+* E) xc * X.Jᵀ * yc = 1`.

Rewrite using `[cT_col_eq_form]`. Use extensionality with `i j`. Rewrite using `[Subsingleton.elim i j]`. Simplify using `[hfyx]`. Establish `hyx : cT (σ : E →+* E) yc * X.Jᵀ * xc = 1`.

Rewrite using `[cT_col_eq_form]`. Use extensionality with `i j`. Rewrite using `[Subsingleton.elim i j]`. Simplify using `[hH.xy]`. Establish `hSD` using `GlobalTheory.T.hermitian_lattice_self_dual_everywhere F E σ B n X r s hB hX`.

Establish `loc : ∀ v (y : GLoc σ X.Jᵀ v), ∃ q k : GLoc σ X.Jᵀ v, k ∈ stabLoc σ X.Jᵀ X.L v ∧ y = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ X.Jᵀ q).1 * xc.map (inclR (F` using `F) (Fv F v)) = xc.map (inclR (F := F) (Fv F v)) * β.1 := fun v y => if hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v then GlobalTheory.T.hyperbolic_pair_lattice_local_split F E σ hσ n X.Jᵀ hND xc yc hxx hyy hxy hyx X.L hX.lat v hv (hSD v) y else GlobalTheory.T.is …`. Take `⟨a, ha, haK⟩` from `GlobalTheory.T.majorant_frame_commutes_cartan F E σ B n X r s hB hX`. Use `set g' := (ofGAd σ X.J).symm g with hg'`. Use `choose qa ka hka hga βa hβa using fun w => GlobalTheory.T.archimedean_iwasawa_majorant_frame F E σ hσ n X.Jᵀ hND xc yc hxx hyx a ha w (projArch σ X.Jᵀ w g')`. Use `choose qf kf hkf hgf βf hβf using fun v => loc v (proj σ X.Jᵀ v g')`.

Use `set S := (Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ X.Jᵀ X.L g')).toFinset with hS`. Take `⟨pa, hpa1, hpa2⟩` from `exists_arch_comp σ X.Jᵀ qa`. Take `⟨pf, hpf1, hpf2⟩` from `exists_fin_comp σ X.Jᵀ qf S`. Use `set p := pa * pf with hp`. Establish `pA : ∀ w, projArch σ X.Jᵀ w p = qa w` using `fun w => by rw [hp, map_mul, hpa2 w, hpf1 w, mul_one]`.

Establish `pF : ∀ v, proj σ X.Jᵀ v p = if v ∈ S then qf v else 1` using `fun v => by rw [hp, map_mul, hpa1 v, hpf2 v, one_mul]`. Take `⟨l, hl⟩` from `GlobalTheory.T.parabolic_archimedean_eigenvector F E σ n X.Jᵀ xc (cT (σ : E →+* E) yc * X.Jᵀ) hyx p (fun w => ⟨βa w, by rw [pA w]; exact hβa w⟩) (fun v => by`. Rewrite using `[pF v]`. Use `split_ifs`. Conclude with `⟨βf v, hβf v⟩`.

Conclude with `⟨1, by simp⟩)`. Use `⟨ofGAd σ X.J p, ⟨l, ?_⟩, ofGAd σ X.J (p⁻¹ * g'), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mat_ofGAd]`. Use function extensionality and compare the values at `i`. Use `congrFun (congrFun hl i) 0` as an intermediate fact.

Simplify `this` using `[adMat, xc, incV, Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Use `GlobalTheory.T.majorant_stabilizer_iwasawa_line F E σ B n X hX.lat _ (fun w => ?_) (fun v => ?_)` and prove the remaining obligations. Establish `e : projArch σ X.Jᵀ w (p⁻¹ * g') = ka w`. Rewrite using `[map_mul, map_inv, pA w, hga w, inv_mul_cancel_left]`. Rewrite using `[e]`.

Conclude with `haK w (ka w) (hka w)`. Establish `e1 : proj σ X.Jᵀ v (p⁻¹ * g') = (if v ∈ S then qf v else 1)⁻¹ * proj σ X.Jᵀ v g'`. Rewrite using `[map_mul, map_inv, pF v]`. Rewrite using `[e1]`. Use `split_ifs with hv`.

Rewrite using `[hgf v, inv_mul_cancel_left]`. Conclude with `hkf v`. Rewrite using `[inv_one, one_mul]`. Assume the negation of the conclusion as `hc`. Conclude with `hv ((Set.Finite.mem_toFinset _).2 hc)`.

Rewrite using `[← map_mul, mul_inv_cancel_left, hg', MulEquiv.apply_symm_apply]`.
-/
theorem iwasawa (B : Base F E) {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {r s : ℕ} {H : Plane E n n₁} {i₀ i₁ : ℕ}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁) (g : UA σ X.J) :
    ∃ p ∈ lineStab σ X.J H.x, ∃ k ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X, g = p * k := by
  classical
  haveI : X.L.IsLattice E := hX.lat
  have hσ : IsCMExt F E σ := hB.cm
  have hs : ∀ z : E, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hσ.2.2.2, hσ.2.2.2, star_star])
  have hND : IsHermND σ X.Jᵀ := isHermND_transpose hX
  set xc : Matrix (Fin n) (Fin 1) E := Matrix.of fun i _ => H.x i with hxc
  set yc : Matrix (Fin n) (Fin 1) E := Matrix.of fun i _ => H.y i with hyc
  have hfyx : form σ X.J H.y H.x = 1 := by
    have e : form σ X.J H.y H.x = σ (form σ X.J H.x H.y) := by
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hs, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [← hX.herm k l, hs]; ring
    rw [e, hH.xy, map_one]
  have hxx : cT (σ : E →+* E) xc * X.Jᵀ * xc = 0 := by
    rw [cT_col_eq_form]; ext i j; simp [hH.xx]
  have hyy : cT (σ : E →+* E) yc * X.Jᵀ * yc = 0 := by
    rw [cT_col_eq_form]; ext i j; simp [hH.yy]
  have hxy : cT (σ : E →+* E) xc * X.Jᵀ * yc = 1 := by
    rw [cT_col_eq_form]; ext i j; rw [Subsingleton.elim i j]; simp [hfyx]
  have hyx : cT (σ : E →+* E) yc * X.Jᵀ * xc = 1 := by
    rw [cT_col_eq_form]; ext i j; rw [Subsingleton.elim i j]; simp [hH.xy]
  have hSD := GlobalTheory.T.hermitian_lattice_self_dual_everywhere F E σ B n X r s hB hX
  have loc : ∀ v (y : GLoc σ X.Jᵀ v), ∃ q k : GLoc σ X.Jᵀ v, k ∈ stabLoc σ X.Jᵀ X.L v ∧ y = q * k ∧
      ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ X.Jᵀ q).1 * xc.map (inclR (F := F) (Fv F v)) =
        xc.map (inclR (F := F) (Fv F v)) * β.1 := fun v y =>
    if hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v then
      GlobalTheory.T.hyperbolic_pair_lattice_local_split F E σ hσ n X.Jᵀ hND xc yc hxx hyy hxy hyx X.L hX.lat v hv (hSD v) y
    else GlobalTheory.T.isotropic_vector_lattice_local F E σ hσ hB.unram n X.Jᵀ hND xc yc hxx hyx X.L hX.lat v hv (hSD v) y
  obtain ⟨a, ha, haK⟩ := GlobalTheory.T.majorant_frame_commutes_cartan F E σ B n X r s hB hX
  set g' := (ofGAd σ X.J).symm g with hg'
  choose qa ka hka hga βa hβa using fun w => GlobalTheory.T.archimedean_iwasawa_majorant_frame F E σ hσ n X.Jᵀ hND xc yc hxx hyx a ha w
    (projArch σ X.Jᵀ w g')
  choose qf kf hkf hgf βf hβf using fun v => loc v (proj σ X.Jᵀ v g')
  set S := (Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ X.Jᵀ X.L g')).toFinset with hS
  obtain ⟨pa, hpa1, hpa2⟩ := exists_arch_comp σ X.Jᵀ qa
  obtain ⟨pf, hpf1, hpf2⟩ := exists_fin_comp σ X.Jᵀ qf S
  set p := pa * pf with hp
  have pA : ∀ w, projArch σ X.Jᵀ w p = qa w := fun w => by rw [hp, map_mul, hpa2 w, hpf1 w, mul_one]
  have pF : ∀ v, proj σ X.Jᵀ v p = if v ∈ S then qf v else 1 := fun v => by rw [hp, map_mul, hpa1 v, hpf2 v, one_mul]
  obtain ⟨l, hl⟩ := GlobalTheory.T.parabolic_archimedean_eigenvector F E σ n X.Jᵀ xc (cT (σ : E →+* E) yc * X.Jᵀ) hyx p
    (fun w => ⟨βa w, by rw [pA w]; exact hβa w⟩) (fun v => by
      rw [pF v]
      split_ifs
      · exact ⟨βf v, hβf v⟩
      · exact ⟨1, by simp⟩)
  refine ⟨ofGAd σ X.J p, ⟨l, ?_⟩, ofGAd σ X.J (p⁻¹ * g'), ?_, ?_⟩
  · rw [mat_ofGAd]
    funext i
    have := congrFun (congrFun hl i) 0
    simpa [adMat, xc, incV, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  · refine GlobalTheory.T.majorant_stabilizer_iwasawa_line F E σ B n X hX.lat _ (fun w => ?_) (fun v => ?_)
    · have e : projArch σ X.Jᵀ w (p⁻¹ * g') = ka w := by
        rw [map_mul, map_inv, pA w, hga w, inv_mul_cancel_left]
      rw [e]; exact haK w (ka w) (hka w)
    · have e1 : proj σ X.Jᵀ v (p⁻¹ * g') = (if v ∈ S then qf v else 1)⁻¹ * proj σ X.Jᵀ v g' := by
        rw [map_mul, map_inv, pF v]
      rw [e1]
      split_ifs with hv
      · rw [hgf v, inv_mul_cancel_left]; exact hkf v
      · rw [inv_one, one_mul]
        by_contra hc
        exact hv ((Set.Finite.mem_toFinset _).2 hc)
  · rw [← map_mul, mul_inv_cancel_left, hg', MulEquiv.apply_symm_apply]

end GlobalTheory.IwLine
