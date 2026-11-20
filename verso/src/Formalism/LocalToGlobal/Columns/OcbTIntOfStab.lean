import Formalism.LocalToGlobal.Columns.FirstUnfoldingEqZeroOfNotIntegral

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Tr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

/- English proof (translation)
Unfold `ocbBEnt`. Rewrite using `[ocbS_atN_comp g y hl hs, Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun m _ => ?_)` and prove the remaining obligations. Establish `hz : ((q : E) ^ (LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) l)) = (q : E) ^ (LocE.scE n (fun i => i + 1) m.1 - LocE.scE n (fun i => i + 1) l) * (q : E) ^ (LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) m.1)`. Rewrite using `[← zpow_add₀ hq0]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hz]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ocbT_bEnt_comp (hq0 : (q : E) ≠ 0) {n' c' n c : ℕ} (g : Sp E (n + c) →ₗ[E] Sp E (n + c)) (y : HomE E (n' + c') (n + c))
    {l s : ℕ} (hl : l < n + c) (hs : s < n' + c') :
    ocbBEnt n' n q (g ∘ₗ y) l s = ∑ m : Fin (n + c), ocbBEnt n n q g l m.1 * ocbBEnt n' n q y m.1 s := by
  unfold ocbBEnt
  rw [ocbS_atN_comp g y hl hs, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hz : ((q : E) ^ (LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) l)) =
      (q : E) ^ (LocE.scE n (fun i => i + 1) m.1 - LocE.scE n (fun i => i + 1) l) *
        (q : E) ^ (LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) m.1) := by
    rw [← zpow_add₀ hq0]
    congr 1
    ring
  rw [hz]
  ring

/- English proof (translation)
Take `⟨s, hs, hsx⟩` from `hx`. Rewrite `hsx` using `[mem_stdLat]`. Take `⟨r, hr⟩` from `hsx i`. Conclude with `⟨r, s, hs, by rw [hr]; simp [Algebra.smul_def]⟩`.
-/
private theorem intAt_apply_of_mem_stdAt {N : ℕ} {x : Sp E N} (hx : x ∈ stdAt E N P) (i : Fin N) : IntAt P (x i) := by
  obtain ⟨s, hs, hsx⟩ := hx
  rw [mem_stdLat] at hsx
  obtain ⟨r, hr⟩ := hsx i
  exact ⟨r, s, hs, by rw [hr]; simp [Algebra.smul_def]⟩

/- English proof (translation)
Unfold `LocE.sclLat`. Rewrite using `[Submodule.mem_comap]`. Both sides reduce to the same expression.
-/
private theorem mem_sclLat_iff_scaled_mem_stdAt {N : ℕ} (e : ℕ → ℤ) (x : Sp E N) :
    x ∈ LocE.sclLat P q N e ↔ (fun l : Fin N => ((q : E) ^ e l)⁻¹ * x l) ∈ stdAt E N P := by
  unfold LocE.sclLat
  rw [Submodule.mem_comap]
  rfl

/- English proof (translation)
Use `set e := LocE.scE n (fun i => i + 1) with he`. Set `v : Sp E (n + c)` to `fun i => if (i : ℕ) = m then (q : E) ^ (e m) else 0`. Establish `hv : v ∈ LocE.lamY P q n c (fun i => i + 1)`. Unfold `LocE.lamY`. Rewrite using `[mem_sclLat_iff_scaled_mem_stdAt]`.

Use `⟨1, one_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul, mem_stdLat]`. Introduce `i`. Distinguish the cases in `hi : (i : ℕ) = m`. Use `⟨1, ?_⟩` and prove the remaining obligations.

Simplify using `only [v, hi, if_true, map_one]`. Rewrite using `[← he, inv_mul_cancel₀ (zpow_ne_zero _ hq0)]`. Conclude with `⟨0, by simp [v, hi]⟩`. Establish `hg' : ∀ x, g x ∈ LocE.lamY P q n c (fun i => i + 1) ↔ x ∈ LocE.lamY P q n c (fun i => i + 1)` using `hg`. Establish `hgv` using `(hg' v).2 hv`.

Unfold `LocE.lamY at hgv`. Rewrite `hgv` using `[mem_sclLat_iff_scaled_mem_stdAt]`. Establish `hint` using `intAt_apply_of_mem_stdAt hgv ⟨l, hl⟩`. Establish `hv' : v = ((q : E) ^ (e m)) • Loc.eN E (n + c) m`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `by_cases hi : (i : ℕ) = m <;> simp [v, Loc.eN, hi]`. Use `hint using 1` and compare the differences between its conclusion and the goal. Unfold `ocbBEnt`. Rewrite using `[ocbS_atN_of_lt _ hl]`. Simplify using `only [LinearEquiv.coe_coe, hv', map_smul, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[← he, zpow_sub₀ hq0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ocbT_int_of_stab (hq0 : (q : E) ≠ 0) {n c : ℕ} {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hg : g ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1))) {l m : ℕ} (hl : l < n + c) (hm : m < n + c) :
    IntAt P (ocbBEnt n n q g.toLinearMap l m) := by
  set e := LocE.scE n (fun i => i + 1) with he
  let v : Sp E (n + c) := fun i => if (i : ℕ) = m then (q : E) ^ (e m) else 0
  have hv : v ∈ LocE.lamY P q n c (fun i => i + 1) := by
    unfold LocE.lamY
    rw [mem_sclLat_iff_scaled_mem_stdAt]
    refine ⟨1, one_mem _, ?_⟩
    rw [one_smul, mem_stdLat]
    intro i
    by_cases hi : (i : ℕ) = m
    · refine ⟨1, ?_⟩
      simp only [v, hi, if_true, map_one]
      rw [← he, inv_mul_cancel₀ (zpow_ne_zero _ hq0)]
    · exact ⟨0, by simp [v, hi]⟩
  have hg' : ∀ x, g x ∈ LocE.lamY P q n c (fun i => i + 1) ↔ x ∈ LocE.lamY P q n c (fun i => i + 1) := hg
  have hgv := (hg' v).2 hv
  unfold LocE.lamY at hgv
  rw [mem_sclLat_iff_scaled_mem_stdAt] at hgv
  have hint := intAt_apply_of_mem_stdAt hgv ⟨l, hl⟩
  have hv' : v = ((q : E) ^ (e m)) • Loc.eN E (n + c) m := by
    funext i
    by_cases hi : (i : ℕ) = m <;> simp [v, Loc.eN, hi]
  convert hint using 1
  unfold ocbBEnt
  rw [ocbS_atN_of_lt _ hl]
  simp only [LinearEquiv.coe_coe, hv', map_smul, Pi.smul_apply, smul_eq_mul]
  rw [← he, zpow_sub₀ hq0]
  ring

/- English proof (translation)
Unfold `ocbBEnt`. Rewrite using `[LinearMap.id_apply, ocbS_atN_of_lt _ hl]`. Distinguish the cases in `h : l = s`. Substitute `h` using the available equality. Simplify using `[Loc.eN]`.

Simplify using `[Loc.eN, h]`.
-/
theorem ocbT_bEnt_id {n c l s : ℕ} (hl : l < n + c) :
    ocbBEnt n n q (LinearMap.id : Sp E (n + c) →ₗ[E] Sp E (n + c)) l s = if l = s then 1 else 0 := by
  unfold ocbBEnt
  rw [LinearMap.id_apply, ocbS_atN_of_lt _ hl]
  by_cases h : l = s
  · subst h
    simp [Loc.eN]
  · simp [Loc.eN, h]

/- English proof (translation)
Establish `hsymm : h₀.symm ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1))` using `(stabL E (n + c) _).inv_mem hh₀`. Establish `hI1 : ∀ i m : ℕ, i < n + c → m < n + c → IntAt P (ocbBEnt n n q h₀.toLinearMap i m)` using `fun i m hi hm => ocbT_int_of_stab hq0 hh₀ hi hm`. Establish `hI2 : ∀ i m : ℕ, i < n + c → m < n + c → IntAt P (ocbBEnt n n q h₀.symm.toLinearMap i m)` using `fun i m hi hm => ocbT_int_of_stab hq0 hsymm hi hm`. Establish `hDA : LinearMap.toMatrix' hbar.symm.toLinearMap * LinearMap.toMatrix' hbar.toLinearMap = 1`. Rewrite using `[← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]`.

Establish `hAC : LinearMap.toMatrix' hbar.toLinearMap * (Matrix.of fun i j : Fin (n + c) => redP P (ocbBEnt n n q h₀.symm.toLinearMap i j)) = 1`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Establish `hcomp` using `ocbT_bEnt_comp (n' := n) (c' := c) hq0 h₀.toLinearMap h₀.symm.toLinearMap i.2 j.2`. Rewrite `hcomp` using `[LinearEquiv.comp_symm, ocbT_bEnt_id i.2]`.

Establish `hsum : ∑ m : Fin (n + c), LinearMap.toMatrix' hbar.toLinearMap i m * (Matrix.of fun i j : Fin (n + c) => redP P (ocbBEnt n n q h₀.symm.toLinearMap i j)) m j = redP P (∑ m : Fin (n + c), ocbBEnt n n q h₀.toLinearMap i m * ocbBEnt n n q h₀.symm.toLinearMap m j)`. Rewrite using `[redP_sum _ _ (fun m _ => IntAt.mul (hI1 _ _ i.2 m.2) (hI2 _ _ m.2 j.2))]`. Use `Finset.sum_congr rfl (fun m _ => ?_)` and prove the remaining obligations. Rewrite using `[reduction_mul (hI1 _ _ i.2 m.2) (hI2 _ _ m.2 j.2), Matrix.of_apply, ocbS_atN_toMatrix']`. Use `congr 1`.

Conclude with `(hred₀ _ _ i.2 m.2).2`. Rewrite using `[hsum, ← hcomp, Matrix.one_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[redP_one]`.

Establish `hij' : (i : ℕ) ≠ j` using `fun h => hij (Fin.ext h)`. Simplify using `[hij, hij', redP_zero]`. Establish `hCD : (Matrix.of fun i j : Fin (n + c) => redP P (ocbBEnt n n q h₀.symm.toLinearMap i j)) = LinearMap.toMatrix' hbar.symm.toLinearMap`. Rewrite using `[← Matrix.one_mul (Matrix.of _), ← hDA, Matrix.mul_assoc, hAC, Matrix.mul_one]`. Establish `h1` using `congrFun (congrFun hCD ⟨l, hl⟩) ⟨s, hs⟩`.

Rewrite `h1` using `[Matrix.of_apply, ocbS_atN_toMatrix']`. Conclude with `h1.symm`.
-/
theorem ocbT_red_symm (hq0 : (q : E) ≠ 0) {n c : ℕ} {h₀ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hh₀ : h₀ ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)))
    {hbar : (Fin (n + c) → 𝓞 E ⧸ P.asIdeal) ≃ₗ[𝓞 E ⧸ P.asIdeal] (Fin (n + c) → 𝓞 E ⧸ P.asIdeal)}
    (hred₀ : ocbIsRed P q n c h₀ hbar) {l s : ℕ} (hl : l < n + c) (hs : s < n + c) :
    Loc.atN (hbar.symm (Loc.eN _ (n + c) s)) l = redP P (ocbBEnt n n q h₀.symm.toLinearMap l s) := by
  classical
  have hsymm : h₀.symm ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)) :=
    (stabL E (n + c) _).inv_mem hh₀
  have hI1 : ∀ i m : ℕ, i < n + c → m < n + c → IntAt P (ocbBEnt n n q h₀.toLinearMap i m) :=
    fun i m hi hm => ocbT_int_of_stab hq0 hh₀ hi hm
  have hI2 : ∀ i m : ℕ, i < n + c → m < n + c → IntAt P (ocbBEnt n n q h₀.symm.toLinearMap i m) :=
    fun i m hi hm => ocbT_int_of_stab hq0 hsymm hi hm
  have hDA : LinearMap.toMatrix' hbar.symm.toLinearMap * LinearMap.toMatrix' hbar.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
  have hAC : LinearMap.toMatrix' hbar.toLinearMap *
      (Matrix.of fun i j : Fin (n + c) => redP P (ocbBEnt n n q h₀.symm.toLinearMap i j)) = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have hcomp := ocbT_bEnt_comp (n' := n) (c' := c) hq0 h₀.toLinearMap h₀.symm.toLinearMap i.2 j.2
    rw [LinearEquiv.comp_symm, ocbT_bEnt_id i.2] at hcomp
    have hsum : ∑ m : Fin (n + c), LinearMap.toMatrix' hbar.toLinearMap i m *
        (Matrix.of fun i j : Fin (n + c) => redP P (ocbBEnt n n q h₀.symm.toLinearMap i j)) m j =
        redP P (∑ m : Fin (n + c),
          ocbBEnt n n q h₀.toLinearMap i m * ocbBEnt n n q h₀.symm.toLinearMap m j) := by
      rw [redP_sum _ _ (fun m _ => IntAt.mul (hI1 _ _ i.2 m.2) (hI2 _ _ m.2 j.2))]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [reduction_mul (hI1 _ _ i.2 m.2) (hI2 _ _ m.2 j.2), Matrix.of_apply, ocbS_atN_toMatrix']
      congr 1
      exact (hred₀ _ _ i.2 m.2).2
    rw [hsum, ← hcomp, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [redP_one]
    · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp [hij, hij', redP_zero]
  have hCD : (Matrix.of fun i j : Fin (n + c) => redP P (ocbBEnt n n q h₀.symm.toLinearMap i j)) =
      LinearMap.toMatrix' hbar.symm.toLinearMap := by
    rw [← Matrix.one_mul (Matrix.of _), ← hDA, Matrix.mul_assoc, hAC, Matrix.mul_one]
  have h1 := congrFun (congrFun hCD ⟨l, hl⟩) ⟨s, hs⟩
  rw [Matrix.of_apply, ocbS_atN_toMatrix'] at h1
  exact h1.symm

/- English proof (translation)
Establish `hsymm : h₀.symm ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1))` using `(stabL E (n + c) _).inv_mem hh₀`. Establish `hcomp_int : ∀ (g : Sp E (n + c) →ₗ[E] Sp E (n + c)) (y : HomE E (n' + c') (n + c)), (∀ l m, l < n + c → m < n + c → IntAt P (ocbBEnt n n q g l m)) → (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q (g ∘ₗ …`. Introduce `g y hg hy l s hl hs`. Rewrite using `[ocbT_bEnt_comp hq0 g y hl hs]`. Conclude with `ciIntAt_sum _ _ (fun m _ => IntAt.mul (hg _ _ hl m.2) (hy _ _ m.2 hs))`.

Use `⟨fun y hy => ?_, fun y ybar hy hyb => ?_⟩` and prove the remaining obligations. Establish `h1` using `hsupp _ hy`. Establish `h2` using `hcomp_int h₀.toLinearMap _ (fun l m hl hm => ocbT_int_of_stab hq0 hh₀ hl hm) h1`. Establish `he : h₀.toLinearMap ∘ₗ (h₀.symm.toLinearMap ∘ₗ y) = y`. Rewrite using `[← LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.id_comp]`.

Rewrite `h2` using `[he]`. Then use the resulting hypothesis. Establish `hI` using `hcomp_int h₀.symm.toLinearMap y (fun l m hl hm => ocbT_int_of_stab hq0 hsymm hl hm) hy`. Apply `hred _ _ hI` to reduce the goal to its premises. Introduce `l s hl hs`. Establish `hs' : s < n' + c''` using `by omega`.

Rewrite using `[ocbS_atN_comp _ _ hl hs', ocbT_bEnt_comp hq0 _ _ hl hs, redP_sum _ _ (fun m _ => IntAt.mul (ocbT_int_of_stab hq0 hsymm hl m.2) (hy _ _ m.2 hs))]`. Use `Finset.sum_congr rfl (fun m _ => ?_)` and prove the remaining obligations. Rewrite using `[reduction_mul (ocbT_int_of_stab hq0 hsymm hl m.2) (hy _ _ m.2 hs), hyb _ _ m.2 hs]`. Use `congr 1`. Conclude with `ocbT_red_symm hq0 hh₀ hred₀ hl m.2`.
-/
theorem ocbT_trans (hq0 : (q : E) ≠ 0) {K L : Type} [Field K] [Field L] (σ : K →+* L) {n' c' c'' n c : ℕ} (hcc : c' = c'')
    {h₀ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hh₀ : h₀ ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)))
    {hbar : (Fin (n + c) → 𝓞 E ⧸ P.asIdeal) ≃ₗ[𝓞 E ⧸ P.asIdeal] (Fin (n + c) → 𝓞 E ⧸ P.asIdeal)}
    (hred₀ : ocbIsRed P q n c h₀ hbar) (Φ : Loc.SF E K (n' + c') (n + c)) (Φr : Loc.SF (𝓞 E ⧸ P.asIdeal) L (n' + c'') (n + c))
    (hsupp : ∀ y, Φ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (hred : ∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) → σ (Φ y) = Φr ybar) :
    (∀ y, Φ (h₀.symm.toLinearMap ∘ₗ y) ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) ∧
    (∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) →
        σ (Φ (h₀.symm.toLinearMap ∘ₗ y)) = Φr (hbar.symm.toLinearMap ∘ₗ ybar)) := by
  have hsymm : h₀.symm ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)) :=
    (stabL E (n + c) _).inv_mem hh₀
  have hcomp_int : ∀ (g : Sp E (n + c) →ₗ[E] Sp E (n + c)) (y : HomE E (n' + c') (n + c)),
      (∀ l m, l < n + c → m < n + c → IntAt P (ocbBEnt n n q g l m)) →
      (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q (g ∘ₗ y) l s) := by
    intro g y hg hy l s hl hs
    rw [ocbT_bEnt_comp hq0 g y hl hs]
    exact ciIntAt_sum _ _ (fun m _ => IntAt.mul (hg _ _ hl m.2) (hy _ _ m.2 hs))
  refine ⟨fun y hy => ?_, fun y ybar hy hyb => ?_⟩
  · have h1 := hsupp _ hy
    have h2 := hcomp_int h₀.toLinearMap _ (fun l m hl hm => ocbT_int_of_stab hq0 hh₀ hl hm) h1
    have he : h₀.toLinearMap ∘ₗ (h₀.symm.toLinearMap ∘ₗ y) = y := by
      rw [← LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.id_comp]
    rwa [he] at h2
  · have hI := hcomp_int h₀.symm.toLinearMap y (fun l m hl hm => ocbT_int_of_stab hq0 hsymm hl hm) hy
    apply hred _ _ hI
    intro l s hl hs
    have hs' : s < n' + c'' := by omega
    rw [ocbS_atN_comp _ _ hl hs', ocbT_bEnt_comp hq0 _ _ hl hs,
      redP_sum _ _ (fun m _ => IntAt.mul (ocbT_int_of_stab hq0 hsymm hl m.2) (hy _ _ m.2 hs))]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [reduction_mul (ocbT_int_of_stab hq0 hsymm hl m.2) (hy _ _ m.2 hs), hyb _ _ m.2 hs]
    congr 1
    exact ocbT_red_symm hq0 hh₀ hred₀ hl m.2

end Tr

end Formalism.L2.Col
