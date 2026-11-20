import Development.WeilBound.ThetaLifts.LatticeBasics.HgtFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplitOrInertK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsIntAddConjEqOneOfBaseGoodK

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Hgt
open scoped Matrix TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl
open PositivityTheory.ThKH.Iwas
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v : Pl F}
/- English proof (translation)
Establish `e : ∀ (K : Type) [Field K] [NumberField K] (u : Pl K) (a : Fv K u), a ∈ (algebraMap (u.adicCompletionIntegers K) (Fv K u)).range ↔ a ∈ u.adicCompletionIntegers K` using `fun _ _ _ _ a => ⟨by rintro ⟨x, rfl⟩; exact x.2, fun h => ⟨⟨a, h⟩, rfl⟩⟩`. Establish `hc` using `hB.cm`. Break down `_root_.GlobalTheory.KFinLoc.split_or_inert_k F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩` into its components or cases. Use `hasSat_of_family (O := v.adicCompletionIntegers F) (I := Bool) (fun i => cond i (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) (splitProj (τ.comp σ) : Fv F v ⊗[F] E →+* Fv F v)) (fun y z h => split_ext hc τ (h true) (h false)) (fun f => ⟨(splitAlgEquiv hc τ).symm (f true, f false), fun …` and prove the remaining obligations. Consider the cases of `i`.

Conclude with `splitProj_comp_symm hc τ _`. Conclude with `splitProj_symm hc τ _`. Rewrite using `[mem_intLoc_iff_split hc τ, Bool.forall_bool]`. Simplify using `only [cond_false, cond_true, e]`. Conclude with `and_comm`.

Establish `h : w.under (𝓞 F) = v` using `(InertChart.under_eq_iff hw w).2 rfl`. Use `hasSat_of_family (O := w.adicCompletionIntegers E) (I := Unit) (fun _ => toCompl h) (fun y z e => (InertChart.toCompl_bijective hw h).1 (e ())) (fun f => ?_) _ (fun y => ?_) _` and prove the remaining obligations. Take `⟨y, hy⟩` from `(InertChart.toCompl_bijective hw h).2 (f ())`. Conclude with `⟨y, fun _ => hy⟩`. Rewrite using `[InertChart.mem_intLoc_iff hw h]`.

Conclude with `⟨fun hy _ => ⟨⟨_, hy⟩, rfl⟩, fun hy => by obtain ⟨x, hx⟩ := hy (); rw [← hx]; exact x.2⟩`.
-/
theorem hasSat_good_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (v : Pl F) : HasSat (intLoc F E v) (Fin n) := by
  have e : ∀ (K : Type) [Field K] [NumberField K] (u : Pl K) (a : Fv K u),
      a ∈ (algebraMap (u.adicCompletionIntegers K) (Fv K u)).range ↔ a ∈ u.adicCompletionIntegers K :=
    fun _ _ _ _ a => ⟨by rintro ⟨x, rfl⟩; exact x.2, fun h => ⟨⟨a, h⟩, rfl⟩⟩
  have hc := hB.cm
  rcases _root_.GlobalTheory.KFinLoc.split_or_inert_k F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · refine hasSat_of_family (O := v.adicCompletionIntegers F) (I := Bool)
      (fun i => cond i (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) (splitProj (τ.comp σ) : Fv F v ⊗[F] E →+* Fv F v))
      (fun y z h => split_ext hc τ (h true) (h false))
      (fun f => ⟨(splitAlgEquiv hc τ).symm (f true, f false), fun i => ?_⟩) _ (fun y => ?_) _
    · cases i
      · exact splitProj_comp_symm hc τ _
      · exact splitProj_symm hc τ _
    · rw [mem_intLoc_iff_split hc τ, Bool.forall_bool]
      simp only [cond_false, cond_true, e]
      exact and_comm
  · have h : w.under (𝓞 F) = v := (InertChart.under_eq_iff hw w).2 rfl
    refine hasSat_of_family (O := w.adicCompletionIntegers E) (I := Unit) (fun _ => toCompl h)
      (fun y z e => (InertChart.toCompl_bijective hw h).1 (e ())) (fun f => ?_) _ (fun y => ?_) _
    · obtain ⟨y, hy⟩ := (InertChart.toCompl_bijective hw h).2 (f ())
      exact ⟨y, fun _ => hy⟩
    · rw [InertChart.mem_intLoc_iff hw h]
      exact ⟨fun hy _ => ⟨⟨_, hy⟩, rfl⟩, fun hy => by obtain ⟨x, hx⟩ := hy (); rw [← hx]; exact x.2⟩
/- English proof (translation)
Establish `hσ` using `cm_conj_conj hB.cm`. Establish `hL : Y.L.IsLattice E` using `hY.elim (·.lat) (·.lat)`. Take `⟨P, h1, h2⟩` from `Frames.exists_rational_frame Y.L v`. Choose the witnesses or unpack the hypotheses as in `⟨δ, h0, G', hG', b1, b2⟩ : ∃ δ : E, δ ≠ 0 ∧ ∃ G' : Matrix (Fin n) (Fin n) E, G' * (P.1ᵀ * Y.J * P.1.map σ) = 1 ∧ (∀ i j, LocInt v (δ⁻¹ * (P.1ᵀ * Y.J * P.1.map σ) i j)) ∧ ∀ i j, LocInt v (δ * G' i j) := by`. Break down `hY with h | h` into its components or cases.

Conclude with `⟨1, one_ne_zero, gram_loc hJ hL.fg (I := IsIntegral ℤ) (fun z hz b => hz.mul b.2) h.dual isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P h1 h2⟩`. Take `⟨δ, d0, d1, d2⟩` from `exists_locGen (E := E) v`. Conclude with `⟨δ, d0, gram_loc hJ hL.fg (I := InD) (fun z hz b => hz.mul b) h.dual d1 d2 P h1 h2⟩`. Take `⟨t, ht⟩` from `_root_.GlobalTheory.exists_int_add_conj_eq_one_of_base_good_k B hB`. Use `set G := P.1ᵀ * Y.J * P.1.map σ with hG`.

Set `ι` to `inclR (F := F) (E := E) (Fv F v)`. Set `l : (Fv F v ⊗[F] E)ˣ` to `Units.map ι.toMonoidHom (Units.mk0 (δ * ξ) (mul_ne_zero h0 hξ))⁻¹`. Establish `e : l.1 • locGram σ (ξ • Y.Jᵀ) (bc ι P) = (δ⁻¹ • Gᵀ).map ι`. Establish `e1 : locGram σ (ξ • Y.Jᵀ) (bc ι P) = (ξ • Gᵀ).map ι`. Rewrite using `[hG, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.mul_assoc, Matrix.map_mul, Matrix.map_mul]`.

Both sides reduce to the same expression. Rewrite using `[e1]`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `ι (δ * ξ)⁻¹ * ι (ξ * G j i) = ι (δ⁻¹ * G j i)`. Rewrite using `[← map_mul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Use `hasIwasawa_of_frame' σ hσ rfl hh (intLoc F E v) ((1 : Fv F v) ⊗ₜ[F] (t : E)) (tmul_mem_intLoc (one_mem _) t) ?_ (fun z hz => sigR_mem_intLoc σ hz) (bc ι P) l (fun i j => ?_) ⟨(δ • G'ᵀ).map ι, fun i j => (b2 j i).mem, ?_⟩ (_root_.GlobalTheory.ThK.Dbl.Hgt.hasSat_good_k hB v) _ fun …` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : Fv F v) ⊗ₜ[F] (t : E) + (1 : Fv F v) ⊗ₜ[F] (σ t) = 1`. Rewrite using `[← TensorProduct.tmul_add, ht]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(l.1 • locGram σ (ξ • Y.Jᵀ) (bc ι P)) i j ∈ _`. Rewrite using `[e]`. Conclude with `(b1 j i).mem`. Rewrite using `[e, ← Matrix.map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ h0, one_smul, ← Matrix.transpose_mul, mul_eq_one_comm.1 hG', Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem hasIwasawa_fin'_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {Y : Spc F E n} {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    (hJ : Y.J.det ≠ 0) {ξ : E} (hξ : ξ ≠ 0) (hh : ∀ i j, σ ((ξ • Y.Jᵀ) j i) = (ξ • Y.Jᵀ) i j) (v : Pl F) :
    HasIwasawa σ (dblGram finSumFinEquiv (ξ • Y.Jᵀ)) (GlobalTheory.Doubling.KFin σ _ Y.L v) := by
  have hσ := cm_conj_conj hB.cm
  have hL : Y.L.IsLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨P, h1, h2⟩ := Frames.exists_rational_frame Y.L v
  obtain ⟨δ, h0, G', hG', b1, b2⟩ : ∃ δ : E, δ ≠ 0 ∧ ∃ G' : Matrix (Fin n) (Fin n) E, G' * (P.1ᵀ * Y.J * P.1.map σ) = 1 ∧
      (∀ i j, LocInt v (δ⁻¹ * (P.1ᵀ * Y.J * P.1.map σ) i j)) ∧ ∀ i j, LocInt v (δ * G' i j) := by
    rcases hY with h | h
    · exact ⟨1, one_ne_zero, gram_loc hJ hL.fg (I := IsIntegral ℤ) (fun z hz b => hz.mul b.2) h.dual
        isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P h1 h2⟩
    · obtain ⟨δ, d0, d1, d2⟩ := exists_locGen (E := E) v
      exact ⟨δ, d0, gram_loc hJ hL.fg (I := InD) (fun z hz b => hz.mul b) h.dual d1 d2 P h1 h2⟩
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.exists_int_add_conj_eq_one_of_base_good_k B hB
  set G := P.1ᵀ * Y.J * P.1.map σ with hG
  let ι := inclR (F := F) (E := E) (Fv F v)
  let l : (Fv F v ⊗[F] E)ˣ := Units.map ι.toMonoidHom (Units.mk0 (δ * ξ) (mul_ne_zero h0 hξ))⁻¹
  have e : l.1 • locGram σ (ξ • Y.Jᵀ) (bc ι P) = (δ⁻¹ • Gᵀ).map ι := by
    have e1 : locGram σ (ξ • Y.Jᵀ) (bc ι P) = (ξ • Gᵀ).map ι := by
      rw [hG, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_smul, ← Matrix.smul_mul,
        ← Matrix.mul_assoc, Matrix.map_mul, Matrix.map_mul]
      rfl
    rw [e1]
    ext i j
    change ι (δ * ξ)⁻¹ * ι (ξ * G j i) = ι (δ⁻¹ * G j i)
    rw [← map_mul]; congr 1; field_simp
  refine hasIwasawa_of_frame' σ hσ rfl hh (intLoc F E v) ((1 : Fv F v) ⊗ₜ[F] (t : E)) (tmul_mem_intLoc (one_mem _) t) ?_
    (fun z hz => sigR_mem_intLoc σ hz) (bc ι P) l (fun i j => ?_) ⟨(δ • G'ᵀ).map ι, fun i j => (b2 j i).mem, ?_⟩
    (_root_.GlobalTheory.ThK.Dbl.Hgt.hasSat_good_k hB v) _ fun k => mem_KFin_of_frame_integral σ _ (Frames.frame_of_rational P h1 h2) k
  · change (1 : Fv F v) ⊗ₜ[F] (t : E) + (1 : Fv F v) ⊗ₜ[F] (σ t) = 1
    rw [← TensorProduct.tmul_add, ht]
    rfl
  · change (l.1 • locGram σ (ξ • Y.Jᵀ) (bc ι P)) i j ∈ _
    rw [e]
    exact (b1 j i).mem
  · rw [e, ← Matrix.map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ h0, one_smul, ← Matrix.transpose_mul,
      mul_eq_one_comm.1 hG', Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _)]
end GlobalTheory.ThK.Dbl.Hgt
end
end
