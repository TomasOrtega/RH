import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAGrp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapAdInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AAInvTrans

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.CapInv

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB Formalism.FourierDecayAlt.P.JFxE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `hterm : ∀ (C : Fin t → Fin N) (σ : Equiv.Perm (Fin t)), (((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C = W (C ∘ σ) • F (C ∘ σ)`. Introduce `C σ`. Rewrite using `[hF, mul_comm, mul_smul]`. Simplify using `only [Finset.sum_smul, hterm]`. Rewrite using `[← Finset.sum_filter, ← Finset.sum_product']`.

Rewrite using `[← Finset.sum_filter_of_ne (p := Function.Injective) (fun d _ hd => by`. Assume the negation of the conclusion as `h; exact hd (by rw [hF0 d h, smul_zero]))]`. Use `symm`. Use `Finset.sum_bij' (fun p _ => p.1 ∘ p.2) (fun d _ => (d ∘ Tuple.sort (fun l => κ (d l)), (Tuple.sort (fun l => κ (d l)))⁻¹)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp`.

Simplify using `only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp ⊢`. Establish `hC : Function.Injective p.1` using `fun i j h => hp.injective (by simp [h])`. Conclude with `hC.comp p.2.injective`. Introduce `d hd`. Simplify using `only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hd ⊢`.

Establish `hinj : Function.Injective ((fun l => κ (d l)) ∘ Tuple.sort (fun l => κ (d l)))` using `(hκ.comp hd).comp (Tuple.sort _).injective`. Conclude with `(Tuple.monotone_sort (fun l => κ (d l))).strictMono_of_injective hinj`. Introduce `p hp`. Simplify using `only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp`. Establish `hs : p.2⁻¹ = Tuple.sort (fun l => κ ((p.1 ∘ p.2) l))`.

Rewrite using `[Tuple.eq_sort_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `i j hij`. Establish `e : ∀ x, p.2 (p.2⁻¹ x) = x` using `fun x => by rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]`. Simplify using `only [Function.comp_apply, e]`.

Conclude with `hp.monotone hij`. Introduce `i j hij heq`. Establish `e : ∀ x, p.2 (p.2⁻¹ x) = x` using `fun x => by rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]`. Simplify using `only [Function.comp_apply, e] at heq`. Conclude with `absurd (hp.injective heq) (ne_of_lt hij)`.

Rewrite using `[← hs]`. Use `ext1`. Use function extensionality and compare the values at `l`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Introduce `d hd`. Use function extensionality and compare the values at `l`. Simplify using the standard rewrite rules. Introduce `p hp`. Both sides reduce to the same expression.
-/
theorem groupingM {M : Type*} [AddCommGroup M] [Module ℂ M] {t N : ℕ} (κ : Fin N → ℕ) (hκ : Function.Injective κ)
    (F : (Fin t → Fin N) → M)
    (hF : ∀ (d : Fin t → Fin N) (τ : Equiv.Perm (Fin t)), F (d ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • F d)
    (hF0 : ∀ d : Fin t → Fin N, ¬ Function.Injective d → F d = 0) (W : (Fin t → Fin N) → ℂ) :
    ∑ d, W d • F d = ∑ C : Fin t → Fin N,
      if StrictMono (fun l => κ (C l)) then
        (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C else 0 := by
  classical
  have hterm : ∀ (C : Fin t → Fin N) (σ : Equiv.Perm (Fin t)),
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C = W (C ∘ σ) • F (C ∘ σ) := by
    intro C σ
    rw [hF, mul_comm, mul_smul]
  simp only [Finset.sum_smul, hterm]
  rw [← Finset.sum_filter, ← Finset.sum_product']
  rw [← Finset.sum_filter_of_ne (p := Function.Injective) (fun d _ hd => by
    by_contra h; exact hd (by rw [hF0 d h, smul_zero]))]
  symm
  refine Finset.sum_bij' (fun p _ => p.1 ∘ p.2)
    (fun d _ => (d ∘ Tuple.sort (fun l => κ (d l)), (Tuple.sort (fun l => κ (d l)))⁻¹)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp ⊢
    have hC : Function.Injective p.1 := fun i j h => hp.injective (by simp [h])
    exact hC.comp p.2.injective
  · intro d hd
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hd ⊢
    have hinj : Function.Injective ((fun l => κ (d l)) ∘ Tuple.sort (fun l => κ (d l))) :=
      (hκ.comp hd).comp (Tuple.sort _).injective
    exact (Tuple.monotone_sort (fun l => κ (d l))).strictMono_of_injective hinj
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp
    have hs : p.2⁻¹ = Tuple.sort (fun l => κ ((p.1 ∘ p.2) l)) := by
      rw [Tuple.eq_sort_iff]
      constructor
      · intro i j hij
        have e : ∀ x, p.2 (p.2⁻¹ x) = x := fun x => by rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
        simp only [Function.comp_apply, e]
        exact hp.monotone hij
      · intro i j hij heq
        have e : ∀ x, p.2 (p.2⁻¹ x) = x := fun x => by rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
        simp only [Function.comp_apply, e] at heq
        exact absurd (hp.injective heq) (ne_of_lt hij)
    rw [← hs]
    ext1
    · funext l; simp
    · simp
  · intro d hd
    funext l; simp
  · intro p hp; rfl

section values

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Introduce `g hg` and use `(bridge_qminor (Q.EH k r) EH_HC EH_HL EH_HA EH_HS (fun c d => rep_ell (c, d)) (Q.EH k r) EH_HL (fun v c d φ _ g _ => ev_Tm_Lf (Q.EH k r) v c d φ g) a b u f hf g hg).symm`.
-/
theorem qm_ev (f : Mat k r → E) {t : ℕ} (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f) (a b : Fin t → Fin (2 * r + k + 1))
    (u : ℂ) : ∀ g ∈ GV k r,
      qminorOp (Q.EH k r) a b u f g = ev (Q.EH k r) (qminor (Lf k r E) a b u) f g := fun g hg =>
  (bridge_qminor (Q.EH k r) EH_HC EH_HL EH_HA EH_HS (fun c d => rep_ell (c, d)) (Q.EH k r) EH_HL
    (fun v c d φ _ g _ => ev_Tm_Lf (Q.EH k r) v c d φ g) a b u f hf g hg).symm

/- English proof (translation)
Introduce `g hg`. Establish `hT' : ∀ v c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r, ev (Q.EH k r) (Tm (Ead (Lf k r E) y⁻¹ y) v c d) φ g = Top (EHc k r y) v c d φ g`. Introduce `v c d φ hφ g hg`. Rewrite using `[ev_Tm_Ead, Formalism.FourierDecayAlt.P.JFxB.top_apply, EHc_change hy c d φ hφ g hg]`. Conclude with `(bridge_qminor (Q.EH k r) EH_HC EH_HL EH_HA EH_HS (rep_Ead y⁻¹ y) (EHc k r y) (EHc_HL hy) hT' a b u f hf g hg).symm`.
-/
theorem qmc_ev {y : Mat k r} (hy : y ∈ GV k r) (f : Mat k r → E) {t : ℕ} (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f)
    (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) : ∀ g ∈ GV k r,
      qminorOp (EHc k r y) a b u f g = ev (Q.EH k r) (qminor (Ead (Lf k r E) y⁻¹ y) a b u) f g := by
  intro g hg
  have hT' : ∀ v c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r,
      ev (Q.EH k r) (Tm (Ead (Lf k r E) y⁻¹ y) v c d) φ g = Top (EHc k r y) v c d φ g := by
    intro v c d φ hφ g hg
    rw [ev_Tm_Ead, Formalism.FourierDecayAlt.P.JFxB.top_apply, EHc_change hy c d φ hφ g hg]
  exact (bridge_qminor (Q.EH k r) EH_HC EH_HL EH_HA EH_HS (rep_Ead y⁻¹ y) (EHc k r y) (EHc_HL hy) hT' a b u f hf
    g hg).symm

/- English proof (translation)
Introduce `g hg`. Establish `h1` using `qminor_trn (k := k) (r := r) (ContinuousLinearMap.id ℂ E) gv_one hy (Q.EH k r) (EHc k r y) (fun c d f hf => EH_trn _ gv_one hy c d f hf) (fun c d f f₂ h => EH_congr c d f f₂ h) (fun c d m f hf => EHc_ck hy c d m f hf) a b u f hf g hg`. Establish `e : trn (ContinuousLinearMap.id ℂ E) 1 y f = fun x => f (x * y)`. Use function extensionality and compare the values at `x`. Simplify using `[trn]`.

Rewrite `h1` using `[e]`. Rewrite using `[h1]`. Simplify using `[trn]`.
-/
theorem qm_right {y : Mat k r} (hy : y ∈ GV k r) (f : Mat k r → E) {t : ℕ} (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f)
    (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) : ∀ g ∈ GV k r,
      qminorOp (Q.EH k r) a b u (fun x => f (x * y)) g = qminorOp (EHc k r y) a b u f (g * y) := by
  intro g hg
  have h1 := qminor_trn (k := k) (r := r) (ContinuousLinearMap.id ℂ E) gv_one hy (Q.EH k r) (EHc k r y)
    (fun c d f hf => EH_trn _ gv_one hy c d f hf) (fun c d f f₂ h => EH_congr c d f f₂ h)
    (fun c d m f hf => EHc_ck hy c d m f hf) a b u f hf g hg
  have e : trn (ContinuousLinearMap.id ℂ E) 1 y f = fun x => f (x * y) := by
    funext x; simp [trn]
  rw [e] at h1
  rw [h1]
  simp [trn]

end values

section rightAA

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Establish `hs'G : s' ∈ GV k r` using `Sset_sub hs'`. Establish `hgs : g * s' ∈ GV k r` using `gv_mul hg hs'G`. Establish `hQP : s' * s'⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (gv_unit hs'G)`. Use `set F : (Fin r → Fin (2 * r + k + 1)) → E := fun d => ev (Q.EH k r) (qminor (Lf k r E) (C3.xR k r r le_rfl) d u) f (g * s') with hFdef`. Establish `hrow : ∀ D : Fin r → Fin (2 * r + k + 1), qminor (Ead (Lf k r E) s'⁻¹ s') (C3.xR k r r le_rfl) D u = ∑ d : Fin r → Fin (2 * r + k + 1), (∏ j, s' (D j) (d j)) • qminor (Lf k r E) (C3.xR k r r le_rfl) d u`.

Introduce `D`. Rewrite using `[show qminor (Ead (Lf k r E) s'⁻¹ s') (C3.xR k r r le_rfl) D u = qminor (fun i j => ∑ c, ∑ d, (s'⁻¹ c i * s' j d) • Lf k r E c d) (C3.xR k r r le_rfl) D u from rfl]`. Rewrite using `[AAInvW.q_expansion _ _ r (Lf k r E) s'⁻¹ s' (C3.xR k r r le_rfl) D u hQP]`. Simplify using `only [mul_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations. Rewrite using `[show (∑ c : Fin r → Fin (2 * r + k + 1), (∏ j, s'⁻¹ (c j) ((C3.xR k r r le_rfl) j)) • (∏ j, s' (D j) (d j)) • qminor (Lf k r E) c d u) = ∑ c : Fin r → Fin (2 * r + k + 1), (∏ j, s' (D j) (d j)) • (∏ j, s'⁻¹ (c j) ((C3.xR k r r le_rfl) j)) • qminor (Lf k r E) c d u from Finset.su …`. Rewrite using `[← Finset.smul_sum]`. Use `congr 1`. Conclude with `AAInvW.collapse le_rfl (eI k r) (AAInvW.eI_inj k r) (fun i j => (s'⁻¹ : Mat k r) i j) (AAInvW.subset_inverse_column k r z' s' hs') (fun c => qminor (Lf k r E) c d u) (fun c hc => by`.

Take `⟨p, q, hpq, h⟩` from `AAInvW.not_inj hc`. Conclude with `quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds (Lf k r E) c d u p q hpq h)`. Establish `hLHS : ∀ D : Fin r → Fin (2 * r + k + 1), qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) D u (fun x => f (x * s')) g = ∑ d, (∏ j, s' (D j) (d j)) • F d`. Introduce `D`. Rewrite using `[show qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) D u (fun x => f (x * s')) g = qminorOp (Q.EH k r) (C3.xR k r r le_rfl) D u (fun x => f (x * s')) g from rfl, qm_right hs'G f hf (C3.xR k r r le_rfl) D u g hg, qmc_ev hs'G f hf (C3.xR k r r le_rfl) D u (g * s') hgs, hrow D, ev_f …`.

Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[ev_smul]`. Establish `hRHS : ∀ C : Fin r → Fin (2 * r + k + 1), qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) C u f (g * s') = F C` using `fun C => qm_ev f hf (C3.xR k r r le_rfl) C u (g * s') hgs`. Establish `hskew : ∀ (d : Fin r → Fin (2 * r + k + 1)) (τ : Equiv.Perm (Fin r)), F (d ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • F d` using `fun d τ => sk_perm (Q.EH k r) EH_HC EH_HL EH_HA EH_HS EH_HGl (C3.xR k r r le_rfl) u f hf τ d (g * s') hgs`. Establish `hzero : ∀ d : Fin r → Fin (2 * r + k + 1), ¬ Function.Injective d → F d = 0` using `fun d hd => sk_zero (Q.EH k r) EH_HC EH_HL EH_HA EH_HS EH_HGl (C3.xR k r r le_rfl) d u f hf hd (g * s') hgs`.

Unfold `C3.AAop`. Simplify using `only [hLHS, hRHS]`. Establish `h1 : ∀ D : Fin r → Fin (2 * r + k + 1), (if StrictMono D then (Matrix.of fun a l : Fin r => herm (Hpk k r) (g *ᵥ bvec (D l)) (bvec (eI k r (Fin.castLE le_rfl a)))).det • ∑ d : Fin r → Fin (2 * r + k + 1), (∏ j, s' (D j) (d j)) • F d else 0) = ∑ d : Fin r → Fin (2 * r + k + 1), (i …`. Introduce `D`. Use `split_ifs`.

Rewrite using `[Finset.smul_sum]`. Simplify using `only [smul_smul]`. Simplify using the standard rewrite rules. Simplify using `only [h1]`. Rewrite using `[Finset.sum_comm]`.

Simplify using `only [← Finset.sum_smul]`. Rewrite using `[groupingM (fun i => i.val) Fin.val_injective F hskew hzero]`. Use `Finset.sum_congr rfl (fun C _ => ?_)` and prove the remaining obligations. Simplify using `only [AAInvW.strictMono_val_iff]`. Use `split_ifs with hC`.

Use `congr 1`. Simplify using `only [AAInvW.herm_mul_bvec]`. Establish `hM : (Matrix.of fun a l : Fin r => ∑ d, s' d (C l) * herm (Hpk k r) (g *ᵥ bvec d) (bvec (eI k r (Fin.castLE le_rfl a)))) = (Matrix.of fun a d => herm (Hpk k r) (g *ᵥ bvec d) (bvec (eI k r (Fin.castLE le_rfl a)))) * (Matrix.of fun d l => s' d (C l))`. Use extensionality with `a l`. Simplify using `[Matrix.mul_apply, mul_comm]`.

Rewrite using `[hM, AAInvW.cauchyBinet (fun i => i.val) Fin.val_injective]`. Simplify using `only [AAInvW.strictMono_val_iff, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun D _ => ?_)` and prove the remaining obligations. Use `split_ifs with hD`.

Simplify using `only [Matrix.of_apply]`. Rewrite using `[AAInvW.det_transpose_apply (Matrix.of fun i l => s' (D i) (C l)), Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Simplify using `only [Matrix.of_apply, Function.comp_apply]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem right_AAop {z' : Fin (2 * r + k + 1) → ℂ} (f : Mat k r → E) (hf : CkOn ((r : ℕ) : ℕ∞) (GV k r) f)
    {s' : Mat k r} (hs' : s' ∈ Sset k r z') (u : ℂ) {g : Mat k r} (hg : g ∈ GV k r) :
    C3.AAop k r r le_rfl u (fun x => f (x * s')) g = C3.AAop k r r le_rfl u f (g * s') := by
  classical
  have hs'G : s' ∈ GV k r := Sset_sub hs'
  have hgs : g * s' ∈ GV k r := gv_mul hg hs'G
  have hQP : s' * s'⁻¹ = 1 := Matrix.mul_nonsing_inv _ (gv_unit hs'G)
  set F : (Fin r → Fin (2 * r + k + 1)) → E :=
    fun d => ev (Q.EH k r) (qminor (Lf k r E) (C3.xR k r r le_rfl) d u) f (g * s') with hFdef
  have hrow : ∀ D : Fin r → Fin (2 * r + k + 1),
      qminor (Ead (Lf k r E) s'⁻¹ s') (C3.xR k r r le_rfl) D u =
        ∑ d : Fin r → Fin (2 * r + k + 1), (∏ j, s' (D j) (d j)) • qminor (Lf k r E) (C3.xR k r r le_rfl) d u := by
    intro D
    rw [show qminor (Ead (Lf k r E) s'⁻¹ s') (C3.xR k r r le_rfl) D u =
      qminor (fun i j => ∑ c, ∑ d, (s'⁻¹ c i * s' j d) • Lf k r E c d) (C3.xR k r r le_rfl) D u from rfl]
    rw [AAInvW.q_expansion _ _ r (Lf k r E) s'⁻¹ s' (C3.xR k r r le_rfl) D u hQP]
    simp only [mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [show (∑ c : Fin r → Fin (2 * r + k + 1), (∏ j, s'⁻¹ (c j) ((C3.xR k r r le_rfl) j)) • (∏ j, s' (D j) (d j)) •
        qminor (Lf k r E) c d u) = ∑ c : Fin r → Fin (2 * r + k + 1), (∏ j, s' (D j) (d j)) •
        (∏ j, s'⁻¹ (c j) ((C3.xR k r r le_rfl) j)) • qminor (Lf k r E) c d u from
      Finset.sum_congr rfl (fun c _ => smul_comm _ _ _)]
    rw [← Finset.smul_sum]
    congr 1
    exact AAInvW.collapse le_rfl (eI k r) (AAInvW.eI_inj k r) (fun i j => (s'⁻¹ : Mat k r) i j) (AAInvW.subset_inverse_column k r z' s' hs')
      (fun c => qminor (Lf k r E) c d u)
      (fun c hc => by
        obtain ⟨p, q, hpq, h⟩ := AAInvW.not_inj hc
        exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds (Lf k r E) c d u p q hpq h)
  have hLHS : ∀ D : Fin r → Fin (2 * r + k + 1),
      qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) D u (fun x => f (x * s')) g = ∑ d, (∏ j, s' (D j) (d j)) • F d := by
    intro D
    rw [show qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) D u (fun x => f (x * s')) g =
      qminorOp (Q.EH k r) (C3.xR k r r le_rfl) D u (fun x => f (x * s')) g from rfl,
      qm_right hs'G f hf (C3.xR k r r le_rfl) D u g hg, qmc_ev hs'G f hf (C3.xR k r r le_rfl) D u (g * s') hgs, hrow D, ev_fsum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [ev_smul]
  have hRHS : ∀ C : Fin r → Fin (2 * r + k + 1), qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) C u f (g * s') = F C :=
    fun C => qm_ev f hf (C3.xR k r r le_rfl) C u (g * s') hgs
  have hskew : ∀ (d : Fin r → Fin (2 * r + k + 1)) (τ : Equiv.Perm (Fin r)),
      F (d ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • F d := fun d τ =>
    sk_perm (Q.EH k r) EH_HC EH_HL EH_HA EH_HS EH_HGl (C3.xR k r r le_rfl) u f hf τ d (g * s') hgs
  have hzero : ∀ d : Fin r → Fin (2 * r + k + 1), ¬ Function.Injective d → F d = 0 := fun d hd =>
    sk_zero (Q.EH k r) EH_HC EH_HL EH_HA EH_HS EH_HGl (C3.xR k r r le_rfl) d u f hf hd (g * s') hgs
  unfold C3.AAop
  simp only [hLHS, hRHS]
  have h1 : ∀ D : Fin r → Fin (2 * r + k + 1),
      (if StrictMono D then (Matrix.of fun a l : Fin r =>
          herm (Hpk k r) (g *ᵥ bvec (D l)) (bvec (eI k r (Fin.castLE le_rfl a)))).det •
        ∑ d : Fin r → Fin (2 * r + k + 1), (∏ j, s' (D j) (d j)) • F d else 0) =
      ∑ d : Fin r → Fin (2 * r + k + 1), (if StrictMono D then
        (Matrix.of fun a l : Fin r => herm (Hpk k r) (g *ᵥ bvec (D l)) (bvec (eI k r (Fin.castLE le_rfl a)))).det *
          ∏ j, s' (D j) (d j) else 0) • F d := by
    intro D
    split_ifs
    · rw [Finset.smul_sum]; simp only [smul_smul]
    · simp
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [groupingM (fun i => i.val) Fin.val_injective F hskew hzero]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  simp only [AAInvW.strictMono_val_iff]
  split_ifs with hC
  · congr 1
    simp only [AAInvW.herm_mul_bvec]
    have hM : (Matrix.of fun a l : Fin r => ∑ d, s' d (C l) *
          herm (Hpk k r) (g *ᵥ bvec d) (bvec (eI k r (Fin.castLE le_rfl a)))) =
        (Matrix.of fun a d => herm (Hpk k r) (g *ᵥ bvec d) (bvec (eI k r (Fin.castLE le_rfl a)))) *
          (Matrix.of fun d l => s' d (C l)) := by
      ext a l; simp [Matrix.mul_apply, mul_comm]
    rw [hM, AAInvW.cauchyBinet (fun i => i.val) Fin.val_injective]
    simp only [AAInvW.strictMono_val_iff, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun D _ => ?_)
    split_ifs with hD
    · simp only [Matrix.of_apply]
      rw [AAInvW.det_transpose_apply (Matrix.of fun i l => s' (D i) (C l)), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      simp only [Matrix.of_apply, Function.comp_apply]
      ring
    · simp
  · rfl

/- English proof (translation)
Establish `hs'G : s' ∈ GV k r` using `Sset_sub hs'`. Establish `hgs : g * s' ∈ GV k r` using `gv_mul hg hs'G`. Establish `hQP : s' * s'⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (gv_unit hs'G)`. Use `set v : ℂ := ell + (r : ℂ) - 1 with hv`. Use `set H : (Fin r → Fin (2 * r + k + 1)) → E := fun c => ev (Q.EH k r) (qminor (Lf k r E) c (C3.sR k r r le_rfl) v) f (g * s') with hHdef`.

Establish `hLHS : ∀ B : Fin r → Fin (2 * r + k + 1), qminorOp (EabH (Hpk k r)) B (C3.sR k r r le_rfl) v (fun x => f (x * s')) g = ∑ c : Fin r → Fin (2 * r + k + 1), (∏ j, (s'⁻¹ : Mat k r) (c j) (B j)) • H c`. Introduce `B`. Rewrite using `[show qminorOp (EabH (Hpk k r)) B (C3.sR k r r le_rfl) v (fun x => f (x * s')) g = qminorOp (Q.EH k r) B (C3.sR k r r le_rfl) v (fun x => f (x * s')) g from rfl, qm_right hs'G f hf B (C3.sR k r r le_rfl) v g hg, qmc_ev hs'G f hf B (C3.sR k r r le_rfl) v (g * s') hgs, show qminor …`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[ev_fsum]`.

Simplify using `only [ev_smul, mul_smul]`. Rewrite using `[← Finset.smul_sum]`. Use `congr 1`. Conclude with `AAInvW.collapse le_rfl (esI k r) (AAInvW.esI_inj k r) (fun i j => s' j i) (AAInvW.subset_row_star k r z' s' hs') (fun d => ev (Q.EH k r) (qminor (Lf k r E) c d v) f (g * s')) (fun d hd => sk_zero (Q.EH k r) EH_HC EH_HL EH_HA EH_HS EH_HGl c d v f hf hd (g * s') hgs)`. Establish `hRHS : ∀ C : Fin r → Fin (2 * r + k + 1), qminorOp (EabH (Hpk k r)) C (C3.sR k r r le_rfl) v f (g * s') = H C` using `fun C => qm_ev f hf C (C3.sR k r r le_rfl) v (g * s') hgs`.

Establish `hskew : ∀ (c : Fin r → Fin (2 * r + k + 1)) (τ : Equiv.Perm (Fin r)), H (c ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • H c`. Introduce `c τ`. Use `show ev (Q.EH k r) (qminor (Lf k r E) (c ∘ τ) (C3.sR k r r le_rfl) v) f (g * s') = _`. Rewrite using `[quantumMinorRowSkew_holds _ _ r (Lf k r E) c (C3.sR k r r le_rfl) τ v, ev_intCast_mul]`. Establish `hzero : ∀ c : Fin r → Fin (2 * r + k + 1), ¬ Function.Injective c → H c = 0`.

Introduce `c hc`. Take `⟨p, q, hpq, h⟩` from `AAInvW.not_inj hc`. Use `show ev (Q.EH k r) (qminor (Lf k r E) c (C3.sR k r r le_rfl) v) f (g * s') = 0`. Rewrite using `[quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds (Lf k r E) c (C3.sR k r r le_rfl) v p q hpq h]`. Both sides reduce to the same expression.

Unfold `C3.AAvop`. Rewrite using `[← hv]`. Simplify using `only [hLHS, hRHS]`. Establish `h1 : ∀ B : Fin r → Fin (2 * r + k + 1), (if StrictMono (fun l => C3.keyS k r (B l)) then (Matrix.of fun a l : Fin r => (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l)).det • ∑ c : Fin r → Fin (2 * r + k + 1), (∏ j, (s'⁻¹ : Mat k r) (c j) (B j)) • H c else 0) = ∑ c : Fin r → Fi …`. Introduce `B`.

Use `split_ifs`. Rewrite using `[Finset.smul_sum]`. Simplify using `only [smul_smul]`. Simplify using the standard rewrite rules. Simplify using `only [h1]`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul]`. Rewrite using `[groupingM (C3.keyS k r) (AAInvW.keyS_inj k r) H hskew hzero]`. Use `Finset.sum_congr rfl (fun C _ => ?_)` and prove the remaining obligations. Use `split_ifs with hC`.

Use `congr 1`. Simplify using `only [AAInvW.inv_mul_apply]`. Establish `hM : (Matrix.of fun a l : Fin r => ∑ d, (s'⁻¹ : Mat k r) (C l) d * (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) d) = (Matrix.of fun a d => (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) d) * (Matrix.of fun d l => (s'⁻¹ : Mat k r) (C l) d)`. Use extensionality with `a l`. Simplify using `[Matrix.mul_apply, mul_comm]`.

Rewrite using `[hM, AAInvW.cauchyBinet (C3.keyS k r) (AAInvW.keyS_inj k r)]`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun B _ => ?_)` and prove the remaining obligations. Use `split_ifs with hB`.

Simplify using `only [Matrix.of_apply]`. Rewrite using `[AAInvW.det_transpose_apply (Matrix.of fun i l => (s'⁻¹ : Mat k r) (C l) (B i)), Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Simplify using `only [Matrix.of_apply, Function.comp_apply]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem right_AAvop {z' : Fin (2 * r + k + 1) → ℂ} (f : Mat k r → E) (hf : CkOn ((r : ℕ) : ℕ∞) (GV k r) f)
    {s' : Mat k r} (hs' : s' ∈ Sset k r z') (ell : ℂ) {g : Mat k r} (hg : g ∈ GV k r) :
    C3.AAvop k r r le_rfl ell (fun x => f (x * s')) g = C3.AAvop k r r le_rfl ell f (g * s') := by
  classical
  have hs'G : s' ∈ GV k r := Sset_sub hs'
  have hgs : g * s' ∈ GV k r := gv_mul hg hs'G
  have hQP : s' * s'⁻¹ = 1 := Matrix.mul_nonsing_inv _ (gv_unit hs'G)
  set v : ℂ := ell + (r : ℂ) - 1 with hv
  set H : (Fin r → Fin (2 * r + k + 1)) → E :=
    fun c => ev (Q.EH k r) (qminor (Lf k r E) c (C3.sR k r r le_rfl) v) f (g * s') with hHdef
  have hLHS : ∀ B : Fin r → Fin (2 * r + k + 1),
      qminorOp (EabH (Hpk k r)) B (C3.sR k r r le_rfl) v (fun x => f (x * s')) g =
        ∑ c : Fin r → Fin (2 * r + k + 1), (∏ j, (s'⁻¹ : Mat k r) (c j) (B j)) • H c := by
    intro B
    rw [show qminorOp (EabH (Hpk k r)) B (C3.sR k r r le_rfl) v (fun x => f (x * s')) g =
      qminorOp (Q.EH k r) B (C3.sR k r r le_rfl) v (fun x => f (x * s')) g from rfl,
      qm_right hs'G f hf B (C3.sR k r r le_rfl) v g hg, qmc_ev hs'G f hf B (C3.sR k r r le_rfl) v (g * s') hgs,
      show qminor (Ead (Lf k r E) s'⁻¹ s') B (C3.sR k r r le_rfl) v =
        qminor (fun i j => ∑ c, ∑ d, ((s'⁻¹ : Mat k r) c i * s' j d) • Lf k r E c d) B (C3.sR k r r le_rfl) v from rfl,
      AAInvW.q_expansion _ _ r (Lf k r E) s'⁻¹ s' B (C3.sR k r r le_rfl) v hQP, ev_fsum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ev_fsum]
    simp only [ev_smul, mul_smul]
    rw [← Finset.smul_sum]
    congr 1
    exact AAInvW.collapse le_rfl (esI k r) (AAInvW.esI_inj k r) (fun i j => s' j i)
      (AAInvW.subset_row_star k r z' s' hs')
      (fun d => ev (Q.EH k r) (qminor (Lf k r E) c d v) f (g * s'))
      (fun d hd => sk_zero (Q.EH k r) EH_HC EH_HL EH_HA EH_HS EH_HGl c d v f hf hd (g * s') hgs)
  have hRHS : ∀ C : Fin r → Fin (2 * r + k + 1),
      qminorOp (EabH (Hpk k r)) C (C3.sR k r r le_rfl) v f (g * s') = H C :=
    fun C => qm_ev f hf C (C3.sR k r r le_rfl) v (g * s') hgs
  have hskew : ∀ (c : Fin r → Fin (2 * r + k + 1)) (τ : Equiv.Perm (Fin r)),
      H (c ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • H c := by
    intro c τ
    show ev (Q.EH k r) (qminor (Lf k r E) (c ∘ τ) (C3.sR k r r le_rfl) v) f (g * s') = _
    rw [quantumMinorRowSkew_holds _ _ r (Lf k r E) c (C3.sR k r r le_rfl) τ v, ev_intCast_mul]
  have hzero : ∀ c : Fin r → Fin (2 * r + k + 1), ¬ Function.Injective c → H c = 0 := by
    intro c hc
    obtain ⟨p, q, hpq, h⟩ := AAInvW.not_inj hc
    show ev (Q.EH k r) (qminor (Lf k r E) c (C3.sR k r r le_rfl) v) f (g * s') = 0
    rw [quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds (Lf k r E) c (C3.sR k r r le_rfl) v p q hpq h]
    rfl
  unfold C3.AAvop
  rw [← hv]
  simp only [hLHS, hRHS]
  have h1 : ∀ B : Fin r → Fin (2 * r + k + 1),
      (if StrictMono (fun l => C3.keyS k r (B l)) then (Matrix.of fun a l : Fin r =>
          (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l)).det •
        ∑ c : Fin r → Fin (2 * r + k + 1), (∏ j, (s'⁻¹ : Mat k r) (c j) (B j)) • H c else 0) =
      ∑ c : Fin r → Fin (2 * r + k + 1), (if StrictMono (fun l => C3.keyS k r (B l)) then
        (Matrix.of fun a l : Fin r => (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l)).det *
          ∏ j, (s'⁻¹ : Mat k r) (c j) (B j) else 0) • H c := by
    intro B
    split_ifs
    · rw [Finset.smul_sum]; simp only [smul_smul]
    · simp
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [groupingM (C3.keyS k r) (AAInvW.keyS_inj k r) H hskew hzero]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  split_ifs with hC
  · congr 1
    simp only [AAInvW.inv_mul_apply]
    have hM : (Matrix.of fun a l : Fin r => ∑ d, (s'⁻¹ : Mat k r) (C l) d *
          (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) d) =
        (Matrix.of fun a d => (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) d) *
          (Matrix.of fun d l => (s'⁻¹ : Mat k r) (C l) d) := by
      ext a l; simp [Matrix.mul_apply, mul_comm]
    rw [hM, AAInvW.cauchyBinet (C3.keyS k r) (AAInvW.keyS_inj k r)]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun B _ => ?_)
    split_ifs with hB
    · simp only [Matrix.of_apply]
      rw [AAInvW.det_transpose_apply (Matrix.of fun i l => (s'⁻¹ : Mat k r) (C l) (B i)), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      simp only [Matrix.of_apply, Function.comp_apply]
      ring
    · simp
  · rfl

end rightAA

section assembly

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Establish `h1` using `qminor_trn (k := k) (r := r) L gv_one gv_one (Q.EH k r) (Q.EH k r) (fun c d f hf => by`. Introduce `g hg`. Rewrite using `[EH_trn L gv_one gv_one c d f hf g hg, EHc_one])`. Use the proof step `(fun c d f f₂ h => EH_congr c d f f₂ h) (fun c d m f hf => EH_ck c d m f hf) a b u F hF g hg`. Rewrite `h1` using `[trn_one_one, trn_one_one]`.

Conclude with `h1`.
-/
theorem post_qm (L : E →L[ℂ] E) (F : Mat k r → E) {t : ℕ} (hF : CkOn ((t : ℕ) : ℕ∞) (GV k r) F)
    (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) {g : Mat k r} (hg : g ∈ GV k r) :
    qminorOp (EabH (Hpk k r)) a b u (fun x => L (F x)) g = L (qminorOp (EabH (Hpk k r)) a b u F g) := by
  have h1 := qminor_trn (k := k) (r := r) L gv_one gv_one (Q.EH k r) (Q.EH k r)
    (fun c d f hf => by
      intro g hg
      rw [EH_trn L gv_one gv_one c d f hf g hg, EHc_one])
    (fun c d f f₂ h => EH_congr c d f f₂ h) (fun c d m f hf => EH_ck c d m f hf) a b u F hF g hg
  rw [trn_one_one, trn_one_one] at h1
  exact h1

/- English proof (translation)
Simplify using `only [C3.AAop, map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[map_smul, post_qm L F hF _ _ u hg]`. Simplify using the standard rewrite rules.
-/
theorem post_AAop (L : E →L[ℂ] E) (F : Mat k r → E) (hF : CkOn ((r : ℕ) : ℕ∞) (GV k r) F) (u : ℂ)
    {g : Mat k r} (hg : g ∈ GV k r) :
    C3.AAop k r r le_rfl u (fun x => L (F x)) g = L (C3.AAop k r r le_rfl u F g) := by
  simp only [C3.AAop, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [map_smul, post_qm L F hF _ _ u hg]
  · simp

/- English proof (translation)
Simplify using `only [C3.AAvop, map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[map_smul, post_qm L F hF _ _ _ hg]`. Simplify using the standard rewrite rules.
-/
theorem post_AAvop (L : E →L[ℂ] E) (F : Mat k r → E) (hF : CkOn ((r : ℕ) : ℕ∞) (GV k r) F) (ell : ℂ)
    {g : Mat k r} (hg : g ∈ GV k r) :
    C3.AAvop k r r le_rfl ell (fun x => L (F x)) g = L (C3.AAvop k r r le_rfl ell F g) := by
  simp only [C3.AAvop, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [map_smul, post_qm L F hF _ _ _ hg]
  · simp

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

/- English proof (translation)
Use `set s : Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with hsdef`. Use `set s' : Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hs'def`. Establish `hs : s ∈ Sset k r Bs.z` using `⟨_, Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.1, _, (Formalism.QuantumDeterminants.nSubgroup k r).2.2 _ hp.2.1, rfl⟩`. Establish `hs' : s' ∈ Sset k r Bs.z'` using `(Formalism.QuantumDeterminants.sGroup k r Bs.z' Bs.z'_mem).2.1 _ ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw Bs.z', _, hp.2.2.2, by simp⟩ _ ⟨_, hp.2.2.1, 1, (Formalism.QuantumDeterminants.nSubgroup k r).1, by simp⟩`. Establish `hsG` using `Sset_sub hs`.

Establish `hs'G` using `Sset_sub hs'`. Establish `hr : ∀ G : Mat k r → (Wq →L[ℂ] Wp), rho Bs p G = fun x => Lq Bs p (G (s * x * s'))`. Introduce `G`. Rewrite using `[rho_eq_trn']`. Both sides reduce to the same expression.

Establish `hF2 : CkOn ((r : ℕ) : ℕ∞) (GV k r) (fun x => F (s * x * s'))`. Use `CkOn_trn (ContinuousLinearMap.id ℂ _) hsG hs'G hF` as an intermediate fact. Establish `e : trn (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) s s' F = fun x => F (s * x * s')`. Use function extensionality and compare the values at `x`. Simplify using `[trn]`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hsg : s * g ∈ GV k r` using `gv_mul hsG hg`. Establish `hsgU : inUH (Hpk k r) g` using `hg`. Take `⟨l1, l2⟩` from `AAInvW.left_aa _ k r Bs.z r le_rfl u ell (fun y => F (y * s')) s g hs hsgU`. Establish `key1 : C3.AAop k r r le_rfl u (fun x => F (s * x * s')) g = C3.AAop k r r le_rfl u F (s * g * s')`.

Establish `l1' : C3.AAop k r r le_rfl u (fun x => F (s * x * s')) g = C3.AAop k r r le_rfl u (fun y => F (y * s')) (s * g)` using `l1`. Rewrite using `[l1', right_AAop F hF hs' u hsg]`. Establish `key2 : C3.AAvop k r r le_rfl ell (fun x => F (s * x * s')) g = C3.AAvop k r r le_rfl ell F (s * g * s')`. Establish `l2' : C3.AAvop k r r le_rfl ell (fun x => F (s * x * s')) g = C3.AAvop k r r le_rfl ell (fun y => F (y * s')) (s * g)` using `l2`. Rewrite using `[l2', right_AAvop F hF hs' ell hsg]`.

Establish `pA` using `post_AAop (Lq Bs p) (fun x => F (s * x * s')) hF2 u hg`. Establish `pV` using `post_AAvop (Lq Bs p) (fun x => F (s * x * s')) hF2 ell hg`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hr F, hr (C3.AAop k r r le_rfl u F)]`. Conclude with `pA.trans (congrArg (Lq Bs p) key1)`.

Rewrite using `[hr F, hr (C3.AAvop k r r le_rfl ell F)]`. Conclude with `pV.trans (congrArg (Lq Bs p) key2)`.
-/
theorem rho_AA_ck (Bs : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn ((r : ℕ) : ℕ∞) (GV k r) F)
    (u ell : ℂ) {p : SS k r} (hp : Bs.inSS p) {g : Mat k r} (hg : g ∈ GV k r) :
    C3.AAop k r r le_rfl u (rho Bs p F) g = rho Bs p (C3.AAop k r r le_rfl u F) g ∧
      C3.AAvop k r r le_rfl ell (rho Bs p F) g = rho Bs p (C3.AAvop k r r le_rfl ell F) g := by
  set s : Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with hsdef
  set s' : Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hs'def
  have hs : s ∈ Sset k r Bs.z :=
    ⟨_, Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.1, _, (Formalism.QuantumDeterminants.nSubgroup k r).2.2 _ hp.2.1, rfl⟩
  have hs' : s' ∈ Sset k r Bs.z' :=
    (Formalism.QuantumDeterminants.sGroup k r Bs.z' Bs.z'_mem).2.1 _ ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw Bs.z', _, hp.2.2.2, by simp⟩ _
      ⟨_, hp.2.2.1, 1, (Formalism.QuantumDeterminants.nSubgroup k r).1, by simp⟩
  have hsG := Sset_sub hs
  have hs'G := Sset_sub hs'
  have hr : ∀ G : Mat k r → (Wq →L[ℂ] Wp), rho Bs p G = fun x => Lq Bs p (G (s * x * s')) := by
    intro G; rw [rho_eq_trn']; rfl
  have hF2 : CkOn ((r : ℕ) : ℕ∞) (GV k r) (fun x => F (s * x * s')) := by
    have := CkOn_trn (ContinuousLinearMap.id ℂ _) hsG hs'G hF
    have e : trn (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) s s' F = fun x => F (s * x * s') := by
      funext x; simp [trn]
    rwa [e] at this
  have hsg : s * g ∈ GV k r := gv_mul hsG hg
  have hsgU : inUH (Hpk k r) g := hg
  obtain ⟨l1, l2⟩ := AAInvW.left_aa _ k r Bs.z r le_rfl u ell (fun y => F (y * s')) s g hs hsgU
  have key1 : C3.AAop k r r le_rfl u (fun x => F (s * x * s')) g = C3.AAop k r r le_rfl u F (s * g * s') := by
    have l1' : C3.AAop k r r le_rfl u (fun x => F (s * x * s')) g =
        C3.AAop k r r le_rfl u (fun y => F (y * s')) (s * g) := l1
    rw [l1', right_AAop F hF hs' u hsg]
  have key2 : C3.AAvop k r r le_rfl ell (fun x => F (s * x * s')) g =
      C3.AAvop k r r le_rfl ell F (s * g * s') := by
    have l2' : C3.AAvop k r r le_rfl ell (fun x => F (s * x * s')) g =
        C3.AAvop k r r le_rfl ell (fun y => F (y * s')) (s * g) := l2
    rw [l2', right_AAvop F hF hs' ell hsg]
  have pA := post_AAop (Lq Bs p) (fun x => F (s * x * s')) hF2 u hg
  have pV := post_AAvop (Lq Bs p) (fun x => F (s * x * s')) hF2 ell hg
  refine ⟨?_, ?_⟩
  · rw [hr F, hr (C3.AAop k r r le_rfl u F)]
    exact pA.trans (congrArg (Lq Bs p) key1)
  · rw [hr F, hr (C3.AAvop k r r le_rfl ell F)]
    exact pV.trans (congrArg (Lq Bs p) key2)

end assembly

end Formalism.FourierDecayAlt.P.CutMP.CapInv

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB CapInv

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs _ _ y Θ hm`. Establish `key : ∀ (G : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)), (∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), CkOn ((P.r : ℕ) : ℕ∞) (GV P.k P.r) F → ∀ p, Bs.inSS p → ∀ g ∈ GV P.k P.r, G (rho Bs p F) g = rho Bs p (G F) g) → (∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Ma …`. Introduce `G hG hA p hp f hf g hg`. Establish `hgG : g ∈ GV P.k P.r` using `hg.1`. Take `⟨h1, h2, h3, h4⟩` from `hp`.

Establish `ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV P.k P.r` using `gv_mul (gv_inv h1.1) (gv_inv h2.1)`. Establish `hb : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV P.k P.r` using `gv_mul h4.1 h3.1`. Establish `hck : ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (x : B.Mat P.k P.r), x ∈ GV P.k P.r → CkOn (B.opOrder Θ : ℕ∞) (GV P.k P.r) F → CkOn (B.opOrder Θ : ℕ∞) {x} F`. Introduce `F x hx hF g₀ hg₀`. Rewrite `hg₀` using `[Set.mem_singleton_iff]`.

Substitute `hg₀` using the available equality. Conclude with `hF _ hx`. Establish `hfr : CkOn ((P.r : ℕ) : ℕ∞) (GV P.k P.r) f` using `sCkOn_mono (by exact_mod_cast hm) hf`. Establish `hrho : CkOn (B.opOrder Θ : ℕ∞) (GV P.k P.r) (rho Bs p f)`. Rewrite using `[rho_eq_trn']`.

Conclude with `CkOn_trn _ ha hb hf`. Establish `hx : sgs p g ∈ GV P.k P.r`. Rewrite using `[show sgs p g = (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * (Matrix.of p.2.2 * Matrix.of p.2.1) by`. Simplify using `[sgs, Matrix.mul_assoc]]`. Conclude with `gv_mul (gv_mul ha hgG) hb`.

Rewrite using `[hA _ g hgG (hck _ g hgG hrho), hG f hfr p ⟨h1, h2, h3, h4⟩ g hgG]`. Simplify using `only [rho]`. Rewrite using `[hA f (sgs p g) hx (hck f _ hx hf)]`. Prove the components needed by the constructor for the conclusion. Conclude with `key _ fun F hF p hp g hg => (rho_AA_ck Bs hF (Q.uC P.k P.r 0 y) 0 hp hg).1`.

Conclude with `key _ fun F hF p hp g hg => (rho_AA_ck Bs hF 0 (y - ((2 * P.r + P.k : ℕ) : ℂ) / 2) hp hg).2`.
-/
theorem capelli_invariance_criterion : JDACapInv := by
  intro Wp Wq _ _ _ _ _ _ P Bs _ _ y Θ hm
  have key : ∀ (G : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
      (∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), CkOn ((P.r : ℕ) : ℕ∞) (GV P.k P.r) F → ∀ p, Bs.inSS p →
        ∀ g ∈ GV P.k P.r, G (rho Bs p F) g = rho Bs p (G F) g) →
      (∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = G F g) →
        B.Commutes Bs (B.GPos Bs) Θ := by
    intro G hG hA p hp f hf g hg
    have hgG : g ∈ GV P.k P.r := hg.1
    obtain ⟨h1, h2, h3, h4⟩ := hp
    have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV P.k P.r := gv_mul (gv_inv h1.1) (gv_inv h2.1)
    have hb : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV P.k P.r := gv_mul h4.1 h3.1
    have hck : ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (x : B.Mat P.k P.r), x ∈ GV P.k P.r →
        CkOn (B.opOrder Θ : ℕ∞) (GV P.k P.r) F → CkOn (B.opOrder Θ : ℕ∞) {x} F := by
      intro F x hx hF g₀ hg₀
      rw [Set.mem_singleton_iff] at hg₀
      subst hg₀
      exact hF _ hx
    have hfr : CkOn ((P.r : ℕ) : ℕ∞) (GV P.k P.r) f := sCkOn_mono (by exact_mod_cast hm) hf
    have hrho : CkOn (B.opOrder Θ : ℕ∞) (GV P.k P.r) (rho Bs p f) := by
      rw [rho_eq_trn']; exact CkOn_trn _ ha hb hf
    have hx : sgs p g ∈ GV P.k P.r := by
      rw [show sgs p g = (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * (Matrix.of p.2.2 * Matrix.of p.2.1) by
        simp [sgs, Matrix.mul_assoc]]
      exact gv_mul (gv_mul ha hgG) hb
    rw [hA _ g hgG (hck _ g hgG hrho), hG f hfr p ⟨h1, h2, h3, h4⟩ g hgG]
    simp only [rho]
    rw [hA f (sgs p g) hx (hck f _ hx hf)]
  constructor
  · exact key _ fun F hF p hp g hg =>
      (rho_AA_ck Bs hF (Q.uC P.k P.r 0 y) 0 hp hg).1
  · exact key _ fun F hF p hp g hg =>
      (rho_AA_ck Bs hF 0 (y - ((2 * P.r + P.k : ℕ) : ℂ) / 2) hp hg).2

end Formalism.FourierDecayAlt.P.CutMP
