import Formalism.SharpRestriction.GrowthBounds.TableLineDegreeFive
import Formalism.LocalToGlobal.GroupLattices.FockModels.MkP

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

/- English proof (translation)
Simplify using `only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf hg ⊢`. Use `⟨hf.1.mul hg.1, fun l j hlj => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hf.2 l j hlj, hg.2 l j hlj]`.
-/
theorem dualWeyl_mul (R : Type*) [CommRing R] (r n : ℕ) (ν ν' : Fin n → ℕ)
    {f g : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν) (hg : g ∈ dualWeyl R r n ν') :
    f * g ∈ dualWeyl R r n (ν + ν') := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf hg ⊢
  refine ⟨hf.1.mul hg.1, fun l j hlj => ?_⟩
  rw [map_mul, map_mul, hf.2 l j hlj, hg.2 l j hlj]

/- English proof (translation)
Simplify using `only [nablaL, Submodule.mem_comap, Submodule.mem_map, LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply] at hF hG ⊢`. Take `⟨f, hf, hfF⟩` from `hF`. Take `⟨f', hf', hfG⟩` from `hG`. Conclude with `⟨f * f', dualWeyl_mul R k n ν ν' hf hf', by rw [map_mul, map_mul, hfF, hfG]⟩`.
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
Use function extensionality and compare the values at `t`. Establish `h1` using `hl (Fin.le_last t)`. Establish `h2` using `hm (Fin.le_last t)`. Simplify using `only [Pi.add_apply]`. Use linear arithmetic over natural numbers and integers.
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
Simplify using `only [nablaLTw, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearMap.lsmul_apply] at hF hG ⊢`. Take `⟨F0, hF0, rfl⟩` from `hF`. Take `⟨G0, hG0, rfl⟩` from `hG`. Establish `hd : g.det ≠ 0` using `hg.ne_zero`. Use `⟨F0 * G0, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[toNat_add_last lam mu hl hm]`. Conclude with `nablaL_mul R K (m + 1) (m + 1) _ _ g hF0 hG0`. Rewrite using `[smul_mul_smul_comm, ← zpow_add₀ hd, Pi.add_apply, neg_add]`.
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
Establish `hlm : Antitone (lam + mu)` using `hl.add hm`. Unfold `H0 at hF hG ⊢`. Rewrite `hF` using `[if_pos hl]`. Rewrite `hG` using `[if_pos hm]`. Rewrite using `[if_pos hlm]`.

Simplify using `only [Submodule.mem_iInf] at hF hG ⊢`. Introduce `g hg`. Conclude with `nablaLTw_mul O Kf m lam mu hl hm g hg.1 (hF g hg) (hG g hg)`.
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
Introduce `P hP Q hQ`. Establish `hPQ : P * Q ∈ tensorLat R K M * tensorLat R K M'` using `Submodule.mul_mem_mul hP hQ`. Unfold `tensorLat at hPQ ⊢`. Rewrite `hPQ` using `[Submodule.span_mul_span]`. Use `Submodule.span_mono ?_ hPQ` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, ⟨F, hF, rfl⟩, b, ⟨G, hG, rfl⟩, rfl⟩`. Conclude with `⟨fun s => F s * G s, fun s => h s _ (hF s) _ (hG s), by simp only [map_mul, Finset.prod_mul_distrib]⟩`.
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
Unfold `lamAt`. Use `split_ifs`. Both sides reduce to the same expression. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply]`.

Expand and normalize the polynomial expressions, which then agree.
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
Unfold `lamAt`. Use `split_ifs`. Conclude with `h s`. Introduce `i j hij`. Establish `hr : j.rev ≤ i.rev`.

Rewrite `hij`, the goal using `[Fin.le_def]`. Simplify using `only [Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Conclude with `neg_le_neg (h s hr)`.
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
Unfold `Formalism.MainNotions.tableLineDegreeFive.LevelPrimesProviso`. Introduce `O Kf _ _ _ n' m lam0 mu0 Λ hl hm F hF G hG`. Unfold `Hten at hF hG ⊢`. Use `tensorLat_mul O Kf _ _ _ ?_ F hF G hG` and prove the remaining obligations. Introduce `s F' hF' G' hG'`.

Use `show F' * G' ∈ H0 O m (lamAt (lam0 + mu0) s) (Λ s)`. Rewrite using `[lamAt_add]`. Conclude with `mul_mem_riemannRochSpace_add O Kf m _ _ (lamAt_antitone_lemma lam0 hl s) (lamAt_antitone_lemma mu0 hm s) (Λ s) hF' hG'`.
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
