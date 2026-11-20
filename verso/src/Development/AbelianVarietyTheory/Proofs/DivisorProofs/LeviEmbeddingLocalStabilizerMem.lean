import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairLatticeLocalSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicVectorLatticeLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantStabilizerIwasawaLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhereStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv.IwasawaAt

open Formalism.UG (cT bc)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Rewrite using `[matHom_proj]`. Both sides reduce to the same expression.
-/
theorem compFin_mat {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (g : GAd σ J) (r s : Fin n) :
    compFin F E v ((matHom (AF F) σ J g).1 r s) = (matHom (Fv F v) σ J (proj σ J v g)).1 r s := by
  rw [matHom_proj]; rfl

/- English proof (translation)
Rewrite using `[matHom_projArch]`. Both sides reduce to the same expression.
-/
theorem compInf_mat {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F) (g : GAd σ J) (r s : Fin n) :
    compInf F E w ((matHom (AF F) σ J g).1 r s) = (matHom w.Completion σ J (projArch σ J w g)).1 r s := by
  rw [matHom_projArch]; rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h r s u hu`. Use `congrFun (congrFun (h u hu) r) s` as an intermediate fact. Simplify using `using this`. Introduce `h u hu`.

Use extensionality with `r s`. Simplify using `using h r s u hu`.
-/
theorem at_iff_entries {R : Type} [Zero R] {n : ℕ} (ev : AF F → R) (M : Matrix (Fin n) (Fin n) (AE F E)) :
    At ev M ↔ ∀ r s, At ev (M r s) := by
  constructor
  · intro h r s u hu
    have := congrFun (congrFun (h u hu) r) s
    simpa using this
  · intro h u hu
    ext r s
    simpa using h r s u hu

/- English proof (translation)
Establish `hrs` using `(at_iff_entries (evFin F v) (mat g - 1)).1 hg`. Establish `e1 : ∀ r s, (matHom (AF F) σ X.Jᵀ ((GlobalTheory.IwLine.ofGAd σ X.J).symm g)).1 r s = mat g r s` using `fun r s => congrFun (congrFun (GlobalTheory.IwLine.matHom_ofGAd_symm σ X.J g) r) s`. Use `⟨fun u hu => GlobalTheory.AutFunCompare.HA_ext σ X.Jᵀ fun r s => ?_, fun w => GlobalTheory.AutFunCompare.HA_ext σ X.Jᵀ fun r s => ?_⟩` and prove the remaining obligations. Establish `h` using `(at_evFin_iff.1 (hrs r s)).2 u hu`. Rewrite `h` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`.

Rewrite using `[← matHom_apply, ← matHom_apply, map_one, Units.val_one, ← compFin_mat, e1, h]`. Distinguish the cases in `hrs' : r = s`. Substitute `hrs'` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hrs']`.

Establish `h` using `(at_evFin_iff.1 (hrs r s)).1 w`. Rewrite `h` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`. Rewrite using `[← matHom_apply, ← matHom_apply, map_one, Units.val_one, ← compInf_mat, e1, h]`. Distinguish the cases in `hrs' : r = s`. Substitute `hrs'` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hrs']`.
-/
theorem proj_eq_one_of_at {n : ℕ} {X : Spc F E n} {v : Pl F} {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) :
    (∀ u, u ≠ v → proj σ X.Jᵀ u ((GlobalTheory.IwLine.ofGAd σ X.J).symm g) = 1) ∧
    ∀ w, projArch σ X.Jᵀ w ((GlobalTheory.IwLine.ofGAd σ X.J).symm g) = 1 := by
  have hrs := (at_iff_entries (evFin F v) (mat g - 1)).1 hg
  have e1 : ∀ r s, (matHom (AF F) σ X.Jᵀ ((GlobalTheory.IwLine.ofGAd σ X.J).symm g)).1 r s = mat g r s := fun r s =>
    congrFun (congrFun (GlobalTheory.IwLine.matHom_ofGAd_symm σ X.J g) r) s
  refine ⟨fun u hu => GlobalTheory.AutFunCompare.HA_ext σ X.Jᵀ fun r s => ?_,
    fun w => GlobalTheory.AutFunCompare.HA_ext σ X.Jᵀ fun r s => ?_⟩
  · have h := (at_evFin_iff.1 (hrs r s)).2 u hu
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h
    rw [← matHom_apply, ← matHom_apply, map_one, Units.val_one, ← compFin_mat, e1, h]
    by_cases hrs' : r = s
    · subst hrs'; simp
    · simp [Matrix.one_apply_ne hrs']
  · have h := (at_evFin_iff.1 (hrs r s)).1 w
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h
    rw [← matHom_apply, ← matHom_apply, map_one, Units.val_one, ← compInf_mat, e1, h]
    by_cases hrs' : r = s
    · subst hrs'; simp
    · simp [Matrix.one_apply_ne hrs']

/- English proof (translation)
Use `(at_iff_entries (evFin F v) _).2 fun r s => at_evFin_iff.2 ⟨fun w => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, map_sub, sub_eq_zero, GlobalTheory.IwLine.mat_ofGAd, compInf_mat, projArch_emb]`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) r s = _`. Distinguish the cases in `hrs' : r = s`. Substitute `hrs'` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hrs']`. Rewrite using `[Matrix.sub_apply, map_sub, sub_eq_zero, GlobalTheory.IwLine.mat_ofGAd, compFin_mat, proj_emb_ne σ X.Jᵀ hu]`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin n) (Fin n) (Fv F u ⊗[F] E)) r s = _`. Distinguish the cases in `hrs' : r = s`.

Substitute `hrs'` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hrs']`.
-/
theorem ofGAd_emb_mem_UAt {n : ℕ} {X : Spc F E n} (v : Pl F) (k : GLoc σ X.Jᵀ v) :
    GlobalTheory.IwLine.ofGAd σ X.J (emb σ X.Jᵀ v k) ∈ UAt σ X (evFin F v) := by
  refine (at_iff_entries (evFin F v) _).2 fun r s => at_evFin_iff.2 ⟨fun w => ?_, fun u hu => ?_⟩
  · rw [Matrix.sub_apply, map_sub, sub_eq_zero, GlobalTheory.IwLine.mat_ofGAd, compInf_mat, projArch_emb]
    change (1 : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) r s = _
    by_cases hrs' : r = s
    · subst hrs'; simp
    · simp [Matrix.one_apply_ne hrs']
  · rw [Matrix.sub_apply, map_sub, sub_eq_zero, GlobalTheory.IwLine.mat_ofGAd, compFin_mat, proj_emb_ne σ X.Jᵀ hu]
    change (1 : Matrix (Fin n) (Fin n) (Fv F u ⊗[F] E)) r s = _
    by_cases hrs' : r = s
    · subst hrs'; simp
    · simp [Matrix.one_apply_ne hrs']

end GlobalTheory.ThK.LemF.QuotInv.IwasawaAt

namespace GlobalTheory.ThK.LemF.QuotInv.IwasawaAt

open Formalism.UG (cT bc)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use `haveI : X.L.IsLattice E := hX.lat`. Establish `hσ : IsCMExt F E σ` using `hB.cm`. Establish `hs : ∀ z : E, σ (σ z) = z` using `fun z => by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Conclude with `τ.injective (by rw [hσ.2.2.2, hσ.2.2.2, star_star])`.

Establish `hND : IsHermND σ X.Jᵀ` using `GlobalTheory.IwLine.isHermND_transpose hX`. Use `set xc : Matrix (Fin n) (Fin 1) E := Matrix.of fun i _ => H.x i with hxc`. Use `set yc : Matrix (Fin n) (Fin 1) E := Matrix.of fun i _ => H.y i with hyc`. Establish `hfyx : form σ X.J H.y H.x = 1`. Establish `e : form σ X.J H.y H.x = σ (form σ X.J H.x H.y)`.

Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hs, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← hX.herm k l, hs]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, hH.xy, map_one]`. Establish `hxx : cT (σ : E →+* E) xc * X.Jᵀ * xc = 0`. Rewrite using `[GlobalTheory.IwLine.cT_col_eq_form]`. Use extensionality with `i j`. Simplify using `[hH.xx]`.

Establish `hyy : cT (σ : E →+* E) yc * X.Jᵀ * yc = 0`. Rewrite using `[GlobalTheory.IwLine.cT_col_eq_form]`. Use extensionality with `i j`. Simplify using `[hH.yy]`. Establish `hxy : cT (σ : E →+* E) xc * X.Jᵀ * yc = 1`.

Rewrite using `[GlobalTheory.IwLine.cT_col_eq_form]`. Use extensionality with `i j`. Rewrite using `[Subsingleton.elim i j]`. Simplify using `[hfyx]`. Establish `hyx : cT (σ : E →+* E) yc * X.Jᵀ * xc = 1`.

Rewrite using `[GlobalTheory.IwLine.cT_col_eq_form]`. Use extensionality with `i j`. Rewrite using `[Subsingleton.elim i j]`. Simplify using `[hH.xy]`. Establish `hSD` using `GlobalTheory.T.hermitian_lattice_self_dual_everywhere F E σ B n X r s hB hX`.

Use `set g' := (GlobalTheory.IwLine.ofGAd σ X.J).symm x with hg'`. Take `⟨q, k, hk, hy, β, hβ⟩ : ∃ q k : GLoc σ X.Jᵀ v, k ∈ stabLoc σ X.Jᵀ X.L v ∧ proj σ X.Jᵀ v g' = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ X.Jᵀ q).1 * xc.map (inclR (F` from `F) (Fv F v)) = xc.map (inclR (F := F) (Fv F v)) * β.1 := if hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v then GlobalTheory.T.hyperbolic_pair_lattice_local_split F E σ hσ n X.Jᵀ hND xc yc hxx hyy hxy hyx X.L hX.lat v hv (hSD v) _ else GlobalTheory.T.isotropic_vec …`. Use `set kt := emb σ X.Jᵀ v k with hkt`. Establish `hKe : K = GlobalTheory.StabHaar.stabK B X`. Use extensionality with `g`.

Rewrite using `[hK g, GlobalTheory.StabHaar.isStab_stabK B X g]`. Establish `hkK : GlobalTheory.IwLine.ofGAd σ X.J kt ∈ K`. Rewrite using `[hKe]`. Use `GlobalTheory.T.majorant_stabilizer_iwasawa_line F E σ B n X hX.lat kt (fun w => ?_) (fun u => ?_)` and prove the remaining obligations. Rewrite using `[hkt, projArch_emb, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`.

Conclude with `Commute.one_left _`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality. Rewrite using `[hkt, proj_emb_self]`. Conclude with `hk`.

Rewrite using `[hkt, proj_emb_ne σ X.Jᵀ hu]`. Conclude with `one_mem _`. Use `set β₀ : (Fv F v ⊗[F] E)ˣ := Matrix.GeneralLinearGroup.det β with hβ₀`. Use `⟨GlobalTheory.IwLine.ofGAd σ X.J kt, ⟨hkK, ofGAd_emb_mem_UAt v k⟩, GlobalTheory.Doubling.ideleAt F E v β₀, ideleAt_mem v β₀, ?_⟩` and prove the remaining obligations. Take `⟨p, hpd⟩ : ∃ p, p = g' * kt⁻¹` from `⟨_, rfl⟩`.

Establish `hp : x * (GlobalTheory.IwLine.ofGAd σ X.J kt)⁻¹ = GlobalTheory.IwLine.ofGAd σ X.J p`. Rewrite using `[hpd, map_mul, map_inv, hg', MulEquiv.apply_symm_apply]`. Establish `hfin : ∀ u, u ≠ v → proj σ X.Jᵀ u p = 1` using `fun u hu => by`. Rewrite using `[hpd, map_mul, map_inv, (proj_eq_one_of_at hx).1 u hu, hkt, proj_emb_ne σ X.Jᵀ hu, inv_one, one_mul]`. Establish `hinf : ∀ w, projArch σ X.Jᵀ w p = 1` using `fun w => by`.

Rewrite using `[hpd, map_mul, map_inv, (proj_eq_one_of_at hx).2 w, hkt, projArch_emb, inv_one, one_mul]`. Establish `hv : proj σ X.Jᵀ v p = q`. Rewrite using `[hpd, map_mul, map_inv, hy, hkt, proj_emb_self, mul_inv_cancel_right]`. Establish `cF : ∀ u (j : Fin n), compFin F E u (incV F H.x j) = inclR (F` using `F) (Fv F u) (H.x j) := fun u j => by`. Simplify using `[incV, inclR, compFin]`.

Establish `cI : ∀ w (j : Fin n), compInf F E w (incV F H.x j) = inclR (F` using `F) w.Completion (H.x j) := fun w j => by`. Simplify using `[incV, inclR, compInf]`. Rewrite using `[hp, GlobalTheory.IwLine.mat_ofGAd]`. Use function extensionality and compare the values at `i`. Use `GlobalTheory.Doubling.adele_ext (fun w => ?_) (fun u => ?_)` and prove the remaining obligations.

Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, compInf_mat, hinf w, cI]`. Establish `e1 : compInf F E w ((GlobalTheory.Doubling.ideleAt F E v β₀ : (AE F E)ˣ) : AE F E) = 1`. Use `congrArg Units.val (GlobalTheory.Doubling.unitInf_ideleAt (F := F) (E := E) w v β₀)` as an intermediate fact. Simplify `this` using `[GlobalTheory.Doubling.unitInf]`. Rewrite using `[e1, one_mul, map_one, Units.val_one]`.

Simplify using `[Matrix.one_apply]`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, compFin_mat, cF]`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality. Rewrite using `[hv]`.

Establish `e1 : compFin F E u ((GlobalTheory.Doubling.ideleAt F E u β₀ : (AE F E)ˣ) : AE F E) = β.1 0 0`. Use `congrArg Units.val (GlobalTheory.Doubling.unitFin_ideleAt_self (F := F) (E := E) u β₀)` as an intermediate fact. Simplify using `only [GlobalTheory.Doubling.unitFin, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at this`. Rewrite using `[this, hβ₀, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]`. Both sides reduce to the same expression.

Rewrite using `[e1]`. Establish `h2` using `congrFun (congrFun hβ i) 0`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, hxc, Matrix.of_apply, Fin.sum_univ_one] at h2`. Rewrite using `[h2, mul_comm]`. Rewrite using `[hfin u hu]`.

Establish `e1 : compFin F E u ((GlobalTheory.Doubling.ideleAt F E v β₀ : (AE F E)ˣ) : AE F E) = 1`. Use `congrArg Units.val (GlobalTheory.Doubling.unitFin_ideleAt_ne (F := F) (E := E) hu β₀)` as an intermediate fact. Simplify `this` using `[GlobalTheory.Doubling.unitFin]`. Rewrite using `[e1, one_mul, map_one, Units.val_one]`. Simplify using `[Matrix.one_apply]`.
-/
theorem exists_kAt_line (B : Base F E) {n n₁ r s : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁}
    {i₀ i₁ : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁)
    {K : Subgroup (UA σ X.J)} (hK : IsStab B K) (v : Pl F) {x : UA σ X.J} (hx : x ∈ UAt σ X (evFin F v)) :
    ∃ k ∈ KAt K (evFin F v), ∃ c ∈ idelesAt E (evFin F v),
      mat (x * k⁻¹) *ᵥ incV F H.x = ((c : (AE F E)ˣ) : AE F E) • incV F H.x := by
  classical
  haveI : X.L.IsLattice E := hX.lat
  have hσ : IsCMExt F E σ := hB.cm
  have hs : ∀ z : E, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hσ.2.2.2, hσ.2.2.2, star_star])
  have hND : IsHermND σ X.Jᵀ := GlobalTheory.IwLine.isHermND_transpose hX
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
    rw [GlobalTheory.IwLine.cT_col_eq_form]; ext i j; simp [hH.xx]
  have hyy : cT (σ : E →+* E) yc * X.Jᵀ * yc = 0 := by
    rw [GlobalTheory.IwLine.cT_col_eq_form]; ext i j; simp [hH.yy]
  have hxy : cT (σ : E →+* E) xc * X.Jᵀ * yc = 1 := by
    rw [GlobalTheory.IwLine.cT_col_eq_form]; ext i j; rw [Subsingleton.elim i j]; simp [hfyx]
  have hyx : cT (σ : E →+* E) yc * X.Jᵀ * xc = 1 := by
    rw [GlobalTheory.IwLine.cT_col_eq_form]; ext i j; rw [Subsingleton.elim i j]; simp [hH.xy]
  have hSD := GlobalTheory.T.hermitian_lattice_self_dual_everywhere F E σ B n X r s hB hX
  set g' := (GlobalTheory.IwLine.ofGAd σ X.J).symm x with hg'
  obtain ⟨q, k, hk, hy, β, hβ⟩ : ∃ q k : GLoc σ X.Jᵀ v, k ∈ stabLoc σ X.Jᵀ X.L v ∧ proj σ X.Jᵀ v g' = q * k ∧
      ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ X.Jᵀ q).1 * xc.map (inclR (F := F) (Fv F v)) =
        xc.map (inclR (F := F) (Fv F v)) * β.1 :=
    if hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v then
      GlobalTheory.T.hyperbolic_pair_lattice_local_split F E σ hσ n X.Jᵀ hND xc yc hxx hyy hxy hyx X.L hX.lat v hv (hSD v) _
    else GlobalTheory.T.isotropic_vector_lattice_local F E σ hσ hB.unram n X.Jᵀ hND xc yc hxx hyx X.L hX.lat v hv (hSD v) _
  set kt := emb σ X.Jᵀ v k with hkt
  have hKe : K = GlobalTheory.StabHaar.stabK B X := by
    ext g
    rw [hK g, GlobalTheory.StabHaar.isStab_stabK B X g]
  have hkK : GlobalTheory.IwLine.ofGAd σ X.J kt ∈ K := by
    rw [hKe]
    refine GlobalTheory.T.majorant_stabilizer_iwasawa_line F E σ B n X hX.lat kt (fun w => ?_) (fun u => ?_)
    · rw [hkt, projArch_emb, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
      exact Commute.one_left _
    · by_cases hu : u = v
      · subst hu; rw [hkt, proj_emb_self]; exact hk
      · rw [hkt, proj_emb_ne σ X.Jᵀ hu]; exact one_mem _
  set β₀ : (Fv F v ⊗[F] E)ˣ := Matrix.GeneralLinearGroup.det β with hβ₀
  refine ⟨GlobalTheory.IwLine.ofGAd σ X.J kt, ⟨hkK, ofGAd_emb_mem_UAt v k⟩, GlobalTheory.Doubling.ideleAt F E v β₀,
    ideleAt_mem v β₀, ?_⟩
  obtain ⟨p, hpd⟩ : ∃ p, p = g' * kt⁻¹ := ⟨_, rfl⟩
  have hp : x * (GlobalTheory.IwLine.ofGAd σ X.J kt)⁻¹ = GlobalTheory.IwLine.ofGAd σ X.J p := by
    rw [hpd, map_mul, map_inv, hg', MulEquiv.apply_symm_apply]
  have hfin : ∀ u, u ≠ v → proj σ X.Jᵀ u p = 1 := fun u hu => by
    rw [hpd, map_mul, map_inv, (proj_eq_one_of_at hx).1 u hu, hkt, proj_emb_ne σ X.Jᵀ hu, inv_one, one_mul]
  have hinf : ∀ w, projArch σ X.Jᵀ w p = 1 := fun w => by
    rw [hpd, map_mul, map_inv, (proj_eq_one_of_at hx).2 w, hkt, projArch_emb, inv_one, one_mul]
  have hv : proj σ X.Jᵀ v p = q := by
    rw [hpd, map_mul, map_inv, hy, hkt, proj_emb_self, mul_inv_cancel_right]
  have cF : ∀ u (j : Fin n), compFin F E u (incV F H.x j) = inclR (F := F) (Fv F u) (H.x j) := fun u j => by
    simp [incV, inclR, compFin]
  have cI : ∀ w (j : Fin n), compInf F E w (incV F H.x j) = inclR (F := F) w.Completion (H.x j) := fun w j => by
    simp [incV, inclR, compInf]
  rw [hp, GlobalTheory.IwLine.mat_ofGAd]
  funext i
  refine GlobalTheory.Doubling.adele_ext (fun w => ?_) (fun u => ?_)
  · simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, compInf_mat, hinf w, cI]
    have e1 : compInf F E w ((GlobalTheory.Doubling.ideleAt F E v β₀ : (AE F E)ˣ) : AE F E) = 1 := by
      have := congrArg Units.val (GlobalTheory.Doubling.unitInf_ideleAt (F := F) (E := E) w v β₀)
      simpa [GlobalTheory.Doubling.unitInf] using this
    rw [e1, one_mul, map_one, Units.val_one]
    simp [Matrix.one_apply]
  · simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, compFin_mat, cF]
    by_cases hu : u = v
    · subst hu
      rw [hv]
      have e1 : compFin F E u ((GlobalTheory.Doubling.ideleAt F E u β₀ : (AE F E)ˣ) : AE F E) = β.1 0 0 := by
        have := congrArg Units.val (GlobalTheory.Doubling.unitFin_ideleAt_self (F := F) (E := E) u β₀)
        simp only [GlobalTheory.Doubling.unitFin, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at this
        rw [this, hβ₀, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
        rfl
      rw [e1]
      have h2 := congrFun (congrFun hβ i) 0
      simp only [Matrix.mul_apply, Matrix.map_apply, hxc, Matrix.of_apply, Fin.sum_univ_one] at h2
      rw [h2, mul_comm]
    · rw [hfin u hu]
      have e1 : compFin F E u ((GlobalTheory.Doubling.ideleAt F E v β₀ : (AE F E)ˣ) : AE F E) = 1 := by
        have := congrArg Units.val (GlobalTheory.Doubling.unitFin_ideleAt_ne (F := F) (E := E) hu β₀)
        simpa [GlobalTheory.Doubling.unitFin] using this
      rw [e1, one_mul, map_one, Units.val_one]
      simp [Matrix.one_apply]

end GlobalTheory.ThK.LemF.QuotInv.IwasawaAt

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT _ v K hK m₀ hm₀ x`. Take `⟨k, hk, c, hc, hxk⟩` from `GlobalTheory.ThK.LemF.QuotInv.IwasawaAt.exists_kAt_line B hT.base hT.geo.hV hC.hH hK v x.2`. Use `set kk : KAt K (evFin F v) := ⟨k, hk⟩ with hkk`. Use `set t : idelesAt E (evFin F v) := (⟨c, hc⟩ : idelesAt E (evFin F v))⁻¹ with ht`. Use `⟨x * (kIncl K (evFin F v) kk)⁻¹ * m₀ t, ?_, t, kk, by group⟩` and prove the remaining obligations.

Rewrite using `[mem_stabAt]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, kIncl_val]`. Rewrite using `[GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, (hm₀ t).1, Matrix.mulVec_smul, hxk, smul_smul]`. Establish `e : ((t : (AE F E)ˣ) : AE F E) * ((c : (AE F E)ˣ) : AE F E) = 1`. Rewrite using `[ht, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]`.

Rewrite using `[e, one_smul]`.
-/
theorem GlobalTheory.ThK.LemF.QuotInv.IwasawaAt.iwasawa_at : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F),
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ m₀ : idelesAt E (evFin F v) →* UAtSub σ G.V (evFin F v), (∀ t, IsLevi H t.1 (1 : UA σ G₁.V.J) (m₀ t).1) →
    ∀ x : UAtSub σ G.V (evFin F v), ∃ q ∈ stabAt σ G.V (evFin F v) H.x, ∃ t k, x = q * (m₀ t)⁻¹ * kIncl K (evFin F v) k := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT _ v K hK m₀ hm₀ x
  obtain ⟨k, hk, c, hc, hxk⟩ :=
    GlobalTheory.ThK.LemF.QuotInv.IwasawaAt.exists_kAt_line B hT.base hT.geo.hV hC.hH hK v x.2
  set kk : KAt K (evFin F v) := ⟨k, hk⟩ with hkk
  set t : idelesAt E (evFin F v) := (⟨c, hc⟩ : idelesAt E (evFin F v))⁻¹ with ht
  refine ⟨x * (kIncl K (evFin F v) kk)⁻¹ * m₀ t, ?_, t, kk, by group⟩
  rw [mem_stabAt]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, kIncl_val]
  rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, (hm₀ t).1, Matrix.mulVec_smul, hxk, smul_smul]
  have e : ((t : (AE F E)ˣ) : AE F E) * ((c : (AE F E)ˣ) : AE F E) = 1 := by
    rw [ht, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [e, one_smul]
