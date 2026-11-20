import Formalism.SharpRestriction.GrowthBounds.TableLineDegreeFive
import Formalism.LocalToGlobal.GroupLattices.FockModels.MkP

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem dualWeyl_mul (R : Type*) [CommRing R] (r n : ℕ) (ν ν' : Fin n → ℕ)
    {f g : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν) (hg : g ∈ dualWeyl R r n ν') :
    f * g ∈ dualWeyl R r n (ν + ν') := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf hg ⊢
  refine ⟨hf.1.mul hg.1, fun l j hlj => ?_⟩
  rw [map_mul, map_mul, hf.2 l j hlj, hg.2 l j hlj]

/- English proof (translation)
Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem nablaL_mul (R K : Type*) [CommRing R] [Field K] [Algebra R K] (k n : ℕ) (ν ν' : Fin n → ℕ)
    (g : Matrix (Fin k) (Fin k) K) {F G : MvPolynomial (Fin k × Fin n) K}
    (hF : F ∈ nablaL R K k n ν g) (hG : G ∈ nablaL R K k n ν' g) : F * G ∈ nablaL R K k n (ν + ν') g := by
  simp only [nablaL, Submodule.mem_comap, Submodule.mem_map, LinearMap.coe_restrictScalars,
    AlgHom.toLinearMap_apply] at hF hG ⊢
  obtain ⟨f, hf, hfF⟩ := hF
  obtain ⟨f', hf', hfG⟩ := hG
  exact ⟨f * f', dualWeyl_mul R k n ν ν' hf hf', by rw [map_mul, map_mul, hfF, hfG]⟩

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem toNat_add_last {m : ℕ} (lam mu : Fin (m + 1) → ℤ) (hl : Antitone lam) (hm : Antitone mu) :
    (fun t => ((lam + mu) t - (lam + mu) (Fin.last m)).toNat) =
      (fun t => (lam t - lam (Fin.last m)).toNat) + fun t => (mu t - mu (Fin.last m)).toNat := by
  funext t
  have h1 := hl (Fin.le_last t)
  have h2 := hm (Fin.le_last t)
  simp only [Pi.add_apply]
  omega

/- English proof (translation)
Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem nablaLTw_mul (R K : Type*) [CommRing R] [Field K] [Algebra R K] (m : ℕ) (lam mu : Fin (m + 1) → ℤ)
    (hl : Antitone lam) (hm : Antitone mu) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det)
    {F G : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K}
    (hF : F ∈ nablaLTw R K m lam g) (hG : G ∈ nablaLTw R K m mu g) : F * G ∈ nablaLTw R K m (lam + mu) g := by
  simp only [nablaLTw, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearMap.lsmul_apply] at hF hG ⊢
  obtain ⟨F0, hF0, rfl⟩ := hF
  obtain ⟨G0, hG0, rfl⟩ := hG
  have hd : g.det ≠ 0 := hg.ne_zero
  refine ⟨F0 * G0, ?_, ?_⟩
  · rw [toNat_add_last lam mu hl hm]
    exact nablaL_mul R K (m + 1) (m + 1) _ _ g hF0 hG0
  · rw [smul_mul_smul_comm, ← zpow_add₀ hd, Pi.add_apply, neg_add]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem mul_mem_riemannRochSpace_add (O Kf : Type*) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam mu : Fin (m + 1) → ℤ)
    (hl : Antitone lam) (hm : Antitone mu) (Λ : Submodule O (Fin (m + 1) → Kf))
    {F G : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf}
    (hF : F ∈ H0 O m lam Λ) (hG : G ∈ H0 O m mu Λ) : F * G ∈ H0 O m (lam + mu) Λ := by
  have hlm : Antitone (lam + mu) := hl.add hm
  unfold H0 at hF hG ⊢
  rw [if_pos hl] at hF
  rw [if_pos hm] at hG
  rw [if_pos hlm]
  simp only [Submodule.mem_iInf] at hF hG ⊢
  intro g hg
  exact nablaLTw_mul O Kf m lam mu hl hm g hg.1 (hF g hg) (hG g hg)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem tensorLat_mul (R K : Type*) [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S] {k n : ℕ}
    (M M' M'' : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (h : ∀ s, ∀ F ∈ M s, ∀ G ∈ M' s, F * G ∈ M'' s) :
    ∀ P ∈ tensorLat R K M, ∀ Q ∈ tensorLat R K M', P * Q ∈ tensorLat R K M'' := by
  intro P hP Q hQ
  have hPQ : P * Q ∈ tensorLat R K M * tensorLat R K M' := Submodule.mul_mem_mul hP hQ
  unfold tensorLat at hPQ ⊢
  rw [Submodule.span_mul_span] at hPQ
  refine Submodule.span_mono ?_ hPQ
  rintro _ ⟨a, ⟨F, hF, rfl⟩, b, ⟨G, hG, rfl⟩, rfl⟩
  exact ⟨fun s => F s * G s, fun s => h s _ (hF s) _ (hG s), by simp only [map_mul, Finset.prod_mul_distrib]⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Both sides reduce to the same expression. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem lamAt_add {n' m : ℕ} (lam0 mu0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    lamAt (lam0 + mu0) s = lamAt lam0 s + lamAt mu0 s := by
  unfold lamAt
  split_ifs
  · rfl
  · funext i
    simp only [Pi.add_apply]
    ring

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
private lemma lamAt_antitone_lemma {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (h : IsDominant lam0)
    (s : Fin n') : Antitone (lamAt lam0 s) := by
  unfold lamAt
  split_ifs
  · exact h s
  · intro i j hij
    have hr : j.rev ≤ i.rev := by
      rw [Fin.le_def] at hij ⊢
      simp only [Fin.val_rev]
      omega
    exact neg_le_neg (h s hr)

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem products_sections_integral (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.tableLineDegreeFive.LevelPrimesProviso D := by
  unfold Formalism.MainNotions.tableLineDegreeFive.LevelPrimesProviso
  intro O Kf _ _ _ n' m lam0 mu0 Λ hl hm F hF G hG
  unfold Hten at hF hG ⊢
  refine tensorLat_mul O Kf _ _ _ ?_ F hF G hG
  intro s F' hF' G' hG'
  show F' * G' ∈ H0 O m (lamAt (lam0 + mu0) s) (Λ s)
  rw [lamAt_add]
  exact mul_mem_riemannRochSpace_add O Kf m _ _ (lamAt_antitone_lemma lam0 hl s) (lamAt_antitone_lemma mu0 hm s) (Λ s) hF' hG'

end Formalism.L2.G.Model
