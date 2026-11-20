import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PContractA
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PContractD
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PContractE

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.CtrX

open PositivityTheory.Rg.Cz

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def semiS {ι Γ : Type} [Fintype ι] (m : ℕ) (τ0 : ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (c : ι → ℤ) : Submodule ℂ (TV n M (Fin m)) where
  carrier := {ζ | ∀ γ, actT (fun _ : Fin m => τ0) κ ρ γ ζ = (∏ τ, (κ τ γ).det ^ c τ) • ζ}
  add_mem' := by
    intro a b ha hb γ
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_add, ha γ, hb γ, smul_add]
  zero_mem' := by
    intro γ
    simp
  smul_mem' := by
    intro r a ha γ
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_smul, ha γ, smul_comm]

/- English proof (translation)
Establish `hsplit : ∀ f : ι → ℂ, ∏ τ, f τ = f τ0 * ∏ τ ∈ Finset.univ.erase τ0, f τ`. Introduce `f`. Rewrite using `[Finset.mul_prod_erase _ _ (Finset.mem_univ τ0)]`. Rewrite using `[hsplit, hsplit (fun τ => d τ ^ c τ)]`. Establish `hrest : ∏ τ ∈ Finset.univ.erase τ0, d τ ^ (Function.update c τ0 (c τ0 - 1)) τ = ∏ τ ∈ Finset.univ.erase τ0, d τ ^ c τ`.

Use `Finset.prod_congr rfl (fun τ hτ => ?_)` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hτ)]`. Rewrite using `[hrest, Function.update_self, zpow_sub_one₀ hd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_update_zpow {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ℂ) (c : ι → ℤ) (τ0 : ι) (hd : d τ0 ≠ 0) :
    ∏ τ, d τ ^ (Function.update c τ0 (c τ0 - 1)) τ = (d τ0)⁻¹ * ∏ τ, d τ ^ c τ := by
  have hsplit : ∀ f : ι → ℂ, ∏ τ, f τ = f τ0 * ∏ τ ∈ Finset.univ.erase τ0, f τ := by
    intro f
    rw [Finset.mul_prod_erase _ _ (Finset.mem_univ τ0)]
  rw [hsplit, hsplit (fun τ => d τ ^ c τ)]
  have hrest : ∏ τ ∈ Finset.univ.erase τ0, d τ ^ (Function.update c τ0 (c τ0 - 1)) τ = ∏ τ ∈ Finset.univ.erase τ0, d τ ^ c τ := by
    refine Finset.prod_congr rfl (fun τ hτ => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]
  rw [hrest, Function.update_self, zpow_sub_one₀ hd]
  ring

/- English proof (translation)
Conclude with `Matrix.det_ne_zero_of_right_inverse (hK.unit τ γ)`.
-/
theorem det_ne {ι Γ : Type} {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} [Group Γ] [TopologicalSpace Γ]
    (hK : IsKD bar κ) (τ : ι) (γ : Γ) : (κ τ γ).det ≠ 0 := by
  exact Matrix.det_ne_zero_of_right_inverse (hK.unit τ γ)

/- English proof (translation)
Take `⟨hGK, hcomm⟩` from `hT n M ι Γ bar κ E ρ hK hG (Fin m) (fun _ => τ0)`. Set `χ : Γ → ℂ` to `fun γ => ∏ τ, (κ τ γ).det ^ c τ`. Set `Y : Submodule ℂ (TV n M (Fin m))` to `semiS m τ0 κ ρ c`. Establish `hY : ∀ y, y ∈ Y ↔ ∀ γ, actT (fun _ : Fin m => τ0) κ ρ γ y = χ γ • y` using `fun y => Iff.rfl`. Set `Q : TV n M (Fin m) →ₗ[ℂ] TV n M0 (Fin m)` to `LinearMap.compLeft q (Fin m → Fin n)`.

Establish `hQap : ∀ y I, Q y I = q (y I)` using `fun _ _ => rfl`. Establish `hpmY : ∀ σ : Equiv.Perm (Fin m), ∀ y ∈ Y, pm σ y ∈ Y`. Introduce `σ y hy`. Rewrite `hy`, the goal using `[hY]`. Introduce `γ`.

Establish `h` using `congrArg (fun T : Module.End ℂ (TV n M (Fin m)) => T y) (hcomm σ (fun _ => rfl) γ).eq`. Simplify using `only [Module.End.mul_apply] at h`. Rewrite using `[← h, hy γ, map_smul]`. Establish `hOmY : ∀ j : Fin m, ∀ y ∈ Y, Om (E τ0) j y ∈ Y`. Introduce `j y hy`.

Rewrite `hy`, the goal using `[hY]`. Introduce `γ`. Rewrite using `[actT_Om τ0 κ (E τ0) ρ γ (hK.unit τ0 γ) (hG.ad γ τ0) j y, hy γ, map_smul]`. Establish `hQpm : ∀ (σ : Equiv.Perm (Fin m)) y, Q (pm σ y) = pm σ (Q y)`. Introduce `σ y`.

Use function extensionality and compare the values at `I`. Both sides reduce to the same expression. Establish `hQlift : ∀ (B : Module.End ℂ M) (B' : Module.End ℂ M0), q ∘ₗ B = B' ∘ₗ q → ∀ y, Q (lift B y) = lift B' (Q y)`. Introduce `B B' hB y`. Use function extensionality and compare the values at `I`.

Simplify using `only [hQap, lift, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]`. Conclude with `LinearMap.congr_fun hB (y I)`. Establish `hQeAt : ∀ (p : Fin m) (a b : Fin n) y, Q (eAt p a b y) = eAt p a b (Q y)`. Introduce `p a b y`. Use function extensionality and compare the values at `I`.

Simplify using `only [hQap, eAt, LinearMap.pi_apply]`. Apply the tactic sequence `split_ifs <;> simp [hQap]`. Establish `hQOm : ∀ (j : Fin m) y, Q (Om (E τ0) j y) = Om F1 j (Q y)`. Introduce `j y`. Simplify using `only [Om, LinearMap.sum_apply, map_sum, Module.End.mul_apply, hQeAt]`.

Use `Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))` and prove the remaining obligations. Rewrite using `[hQlift _ _ (hq1 a b), hQeAt]`. Establish `hfib1 : fib (fun _ : Fin m => τ0) τ0 = Finset.univ`. Use extensionality with `p`. Simplify using `[fib]`.

Establish `hfib2 : fib (fun _ : Fin m => τ0) (bar τ0) = ∅`. Use extensionality with `p`. Simplify using `[fib, (hK.ne τ0).symm]`. Set `c' : ℂ` to `((c τ0 - c (bar τ0) : ℤ) : ℂ)`. Establish `hQtE : ∀ y ∈ Y, ∀ a b : Fin n, tE Finset.univ (fun a b => F1 a b + -F2 b a) a b (Q y) = if a = b then c' • Q y else 0`.

Introduce `y hy a b`. Establish `h` using `hL n (TV n M (Fin m)) ι Γ bar κ (fun τ => tE (fib (fun _ : Fin m => τ0) τ) (E τ)) (actT (fun _ : Fin m => τ0) κ ρ) hK hGK c y ((hY y).1 hy) τ0 a b`. Simplify using `only [hfib1, hfib2, tE, Finset.sum_empty, add_zero] at h`. Establish `h'` using `congrArg Q h`. Rewrite `h'` using `[map_sub, LinearMap.add_apply, map_add, LinearMap.sum_apply, map_sum, hQlift _ _ (hq1 a b), hQlift _ _ (hq2 b a)]`.

Simplify using `only [hQeAt] at h'`. Establish `hl : ∀ (B1 B2 : Module.End ℂ M0) (v : TV n M0 (Fin m)), lift (B1 + -B2) v = lift B1 v - lift B2 v`. Introduce `B1 B2 v`. Use function extensionality and compare the values at `I`. Simplify using `[lift, sub_eq_add_neg]`.

Simplify using `only [tE, LinearMap.add_apply, hl, LinearMap.sum_apply]`. Rewrite using `[sub_add_eq_add_sub, h']`. Apply the tactic sequence `split_ifs <;> simp [c']`. Set `X : Submodule ℂ (TV n M0 (Fin m))` to `Y.map Q`. Establish `hζY : ζ ∈ Y` using `(hY ζ).2 hζ`.

Establish `hXne : X ≠ ⊥`. Take `⟨I, hI⟩` from `hz`. Introduce `hX`. Establish `hmem : Q ζ ∈ X` using `Submodule.mem_map_of_mem hζY`. Rewrite `hmem` using `[hX, Submodule.mem_bot]`.

Conclude with `hI (by rw [← hQap, hmem]; rfl)`. Establish `hXpm : ∀ σ : Equiv.Perm (Fin m), ∀ ξ ∈ X, pm σ ξ ∈ X`. Introduce `σ ξ hξ`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hξ`. Rewrite using `[← hQpm]`.

Conclude with `Submodule.mem_map_of_mem (hpmY σ y hy)`. Establish `hXOm : ∀ j : Fin m, ∀ ξ ∈ X, Om F1 j ξ ∈ X`. Introduce `j ξ hξ`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hξ`. Rewrite using `[← hQOm]`.

Conclude with `Submodule.mem_map_of_mem (hOmY j y hy)`. Establish `hXtE : ∀ a b : Fin n, ∀ ξ ∈ X, tE Finset.univ (fun a b => F1 a b + -F2 b a) a b ξ = if a = b then c' • ξ else 0`. Introduce `a b ξ hξ`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hξ`. Conclude with `hQtE y hy a b`.

Take `⟨-, -, -, hgl2, hch2⟩` from `hQ n M0 F2 hF2`. Establish `hcomm12 : ∀ a b c d : Fin n, Commute (F1 a b) (-F2 d c)` using `fun a b c d => (hc a b d c).neg_right`. Take `⟨-, hwall⟩` from `hW n M0 F1 (fun a b => -F2 b a) hF1 hgl2 hcomm12 s (-((n : ℂ) - 1) - s) c' hs1 (hch2 _ hs2) m X hXne hXpm hXOm hXtE`. Take `⟨hnm, ξ, hξX, hξalt⟩` from `hwall hm`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hξX`.

Establish `hQalt : Q (alt (firstG m n) y) = alt (firstG m n) (Q y)`. Simplify using `only [alt, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul, hQpm]`. Set `ζ' : TV n M (Fin m)` to `alt (firstG m n) y`. Establish `hζ'Y : ζ' ∈ Y` using `by show (∑ σ ∈ firstG m n, ((Equiv.Perm.sign σ : ℤ) : ℂ) • pm σ) y ∈ Y`. Rewrite using `[LinearMap.sum_apply]`.

Conclude with `Submodule.sum_mem _ (fun σ _ => Submodule.smul_mem _ _ (hpmY σ y hy))`. Establish `hanti : ∀ τ ∈ firstG m n, pm τ ζ' = ((Equiv.Perm.sign τ : ℤ) : ℂ) • ζ'` using `fun τ hτ => pm_alt_firstG τ hτ y`. Establish `hnz : ∃ I, q (ζ' I) ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Apply `hξalt` to reduce the goal to its premises. Rewrite using `[← hQalt]`. Use function extensionality and compare the values at `I`. Rewrite using `[hQap]`. Conclude with `hcon I`.

Use `set e := splitE m n hnm with he`. Set `g : TV n M (Fin (m - n) ⊕ Fin n)` to `reIx e ζ'`. Set `F : TV n (TV n M (Fin (m - n))) (Fin n)` to `cur g`. Establish `hFanti : ∀ σ : Equiv.Perm (Fin n), pm σ F = ((Equiv.Perm.sign σ : ℤ) : ℂ) • F` using `cur_anti hnm ζ' hanti`. Use `⟨m - n, by omega, F id, fun γ => ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : actT (fun _ : Fin (m - n) ⊕ Fin n => τ0) κ ρ γ g = χ γ • g`. Establish `h0` using `actT_reIx e (fun _ : Fin m => τ0) κ ρ γ ζ'`. Rewrite `h0` using `[(hY ζ').1 hζ'Y γ, reIx_smul]`. Conclude with `h0`. Establish `h2 : (fun _ : Fin (m - n) ⊕ Fin n => τ0) = Sum.elim (fun _ : Fin (m - n) => τ0) (fun _ : Fin n => τ0)`.

Use function extensionality and compare the values at `x`. Apply the tactic sequence `cases x <;> rfl`. Establish `h3 : actT (fun _ : Fin n => τ0) κ (actT (fun _ : Fin (m - n) => τ0) κ ρ) γ F = χ γ • F`. Apply `unc_inj` to reduce the goal to its premises. Rewrite using `[← actT_unc, unc_smul, unc_cur, ← h2, h1]`.

Establish `h4` using `actT_anti_id τ0 κ (actT (fun _ : Fin (m - n) => τ0) κ ρ) γ F hFanti`. Rewrite `h4` using `[h3]`. Establish `hdet` using `det_ne hK τ0 γ`. Rewrite using `[prod_update_zpow (fun τ => (κ τ γ).det) c τ0 hdet, mul_smul]`. Establish `h5` using `congrArg (fun v => ((κ τ0 γ).det)⁻¹ • v) h4`.

Simplify using `only [smul_smul, inv_mul_cancel₀ hdet, one_smul, Pi.smul_apply] at h5`. Rewrite using `[← h5, smul_smul]`. Take `⟨I, hI⟩` from `hnz`. Set `K : Fin (m - n) → Fin n` to `fun k => I (e.symm (Sum.inl k))`. Set `J : Fin n → Fin n` to `fun j => I (e.symm (Sum.inr j))`.

Take `⟨a, ha⟩` from `anti_span F hFanti J`. Use `⟨K, fun hK0 => hI ?_⟩` and prove the remaining obligations. Establish `hIe : Sum.elim K J ∘ e = I`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply]`.

Generalize the expression as in `hy : e x = w`. Consider the cases of `w with`. Consider the case `inl k => show I (e.symm (Sum.inl k)) = I x`. Rewrite using `[← hy, Equiv.symm_apply_apply]`. Consider the case `inr k => show I (e.symm (Sum.inr k)) = I x`.

Rewrite using `[← hy, Equiv.symm_apply_apply]`. Establish `h6 : ζ' I = F J K` using `by show ζ' I = ζ' (Sum.elim K J ∘ e)`. Rewrite using `[hIe]`. Rewrite using `[h6, ha, Pi.smul_apply, map_smul, hK0, smul_zero]`.
-/
theorem core (hQ : QdetFacts) (hW : WallAlg) (hT : TensorGK) (hL : LieInv)
    {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
    {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} {E : ι → Fin n → Fin n → Module.End ℂ M}
    {ρ : Γ → Module.End ℂ M} (hK : IsKD bar κ) (hG : IsGK bar κ E ρ) (τ0 : ι)
    {M0 : Type} [AddCommGroup M0] [Module ℂ M0] (q : M →ₗ[ℂ] M0) (F1 F2 : Fin n → Fin n → Module.End ℂ M0)
    (s : ℂ) (hF1 : GlRel F1) (hF2 : GlRel F2) (hc : ∀ a b c d, Commute (F1 a b) (F2 c d))
    (hs1 : HasChar F1 fun _ => s) (hs2 : HasChar F2 fun _ => s)
    (hq1 : ∀ a b, q ∘ₗ E τ0 a b = F1 a b ∘ₗ q) (hq2 : ∀ a b, q ∘ₗ E (bar τ0) a b = F2 a b ∘ₗ q)
    (hn : 1 ≤ n) (m : ℕ) (hm : 0 < m) (c : ι → ℤ) (ζ : TV n M (Fin m))
    (hζ : ∀ γ, actT (fun _ : Fin m => τ0) κ ρ γ ζ = (∏ τ, (κ τ γ).det ^ c τ) • ζ) (hz : ∃ I, q (ζ I) ≠ 0) :
    ∃ m2 < m, ∃ ζ2 : TV n M (Fin m2), (∀ γ, actT (fun _ : Fin m2 => τ0) κ ρ γ ζ2 =
      (∏ τ, (κ τ γ).det ^ (Function.update c τ0 (c τ0 - 1)) τ) • ζ2) ∧ ∃ I, q (ζ2 I) ≠ 0 := by
  classical
  obtain ⟨hGK, hcomm⟩ := hT n M ι Γ bar κ E ρ hK hG (Fin m) (fun _ => τ0)
  let χ : Γ → ℂ := fun γ => ∏ τ, (κ τ γ).det ^ c τ
  let Y : Submodule ℂ (TV n M (Fin m)) := semiS m τ0 κ ρ c
  have hY : ∀ y, y ∈ Y ↔ ∀ γ, actT (fun _ : Fin m => τ0) κ ρ γ y = χ γ • y := fun y => Iff.rfl
  let Q : TV n M (Fin m) →ₗ[ℂ] TV n M0 (Fin m) := LinearMap.compLeft q (Fin m → Fin n)
  have hQap : ∀ y I, Q y I = q (y I) := fun _ _ => rfl
  have hpmY : ∀ σ : Equiv.Perm (Fin m), ∀ y ∈ Y, pm σ y ∈ Y := by
    intro σ y hy
    rw [hY] at hy ⊢
    intro γ
    have h := congrArg (fun T : Module.End ℂ (TV n M (Fin m)) => T y) (hcomm σ (fun _ => rfl) γ).eq
    simp only [Module.End.mul_apply] at h
    rw [← h, hy γ, map_smul]
  have hOmY : ∀ j : Fin m, ∀ y ∈ Y, Om (E τ0) j y ∈ Y := by
    intro j y hy
    rw [hY] at hy ⊢
    intro γ
    rw [actT_Om τ0 κ (E τ0) ρ γ (hK.unit τ0 γ) (hG.ad γ τ0) j y, hy γ, map_smul]
  have hQpm : ∀ (σ : Equiv.Perm (Fin m)) y, Q (pm σ y) = pm σ (Q y) := by
    intro σ y
    funext I
    rfl
  have hQlift : ∀ (B : Module.End ℂ M) (B' : Module.End ℂ M0), q ∘ₗ B = B' ∘ₗ q → ∀ y, Q (lift B y) = lift B' (Q y) := by
    intro B B' hB y
    funext I
    simp only [hQap, lift, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    exact LinearMap.congr_fun hB (y I)
  have hQeAt : ∀ (p : Fin m) (a b : Fin n) y, Q (eAt p a b y) = eAt p a b (Q y) := by
    intro p a b y
    funext I
    simp only [hQap, eAt, LinearMap.pi_apply]
    split_ifs <;> simp [hQap]
  have hQOm : ∀ (j : Fin m) y, Q (Om (E τ0) j y) = Om F1 j (Q y) := by
    intro j y
    simp only [Om, LinearMap.sum_apply, map_sum, Module.End.mul_apply, hQeAt]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hQlift _ _ (hq1 a b), hQeAt]
  have hfib1 : fib (fun _ : Fin m => τ0) τ0 = Finset.univ := by
    ext p
    simp [fib]
  have hfib2 : fib (fun _ : Fin m => τ0) (bar τ0) = ∅ := by
    ext p
    simp [fib, (hK.ne τ0).symm]
  let c' : ℂ := ((c τ0 - c (bar τ0) : ℤ) : ℂ)
  have hQtE : ∀ y ∈ Y, ∀ a b : Fin n, tE Finset.univ (fun a b => F1 a b + -F2 b a) a b (Q y) = if a = b then c' • Q y else 0 := by
    intro y hy a b
    have h := hL n (TV n M (Fin m)) ι Γ bar κ (fun τ => tE (fib (fun _ : Fin m => τ0) τ) (E τ)) (actT (fun _ : Fin m => τ0) κ ρ) hK hGK c y ((hY y).1 hy) τ0 a b
    simp only [hfib1, hfib2, tE, Finset.sum_empty, add_zero] at h
    have h' := congrArg Q h
    rw [map_sub, LinearMap.add_apply, map_add, LinearMap.sum_apply, map_sum, hQlift _ _ (hq1 a b), hQlift _ _ (hq2 b a)] at h'
    simp only [hQeAt] at h'
    have hl : ∀ (B1 B2 : Module.End ℂ M0) (v : TV n M0 (Fin m)), lift (B1 + -B2) v = lift B1 v - lift B2 v := by
      intro B1 B2 v
      funext I
      simp [lift, sub_eq_add_neg]
    simp only [tE, LinearMap.add_apply, hl, LinearMap.sum_apply]
    rw [sub_add_eq_add_sub, h']
    split_ifs <;> simp [c']
  let X : Submodule ℂ (TV n M0 (Fin m)) := Y.map Q
  have hζY : ζ ∈ Y := (hY ζ).2 hζ
  have hXne : X ≠ ⊥ := by
    obtain ⟨I, hI⟩ := hz
    intro hX
    have hmem : Q ζ ∈ X := Submodule.mem_map_of_mem hζY
    rw [hX, Submodule.mem_bot] at hmem
    exact hI (by rw [← hQap, hmem]; rfl)
  have hXpm : ∀ σ : Equiv.Perm (Fin m), ∀ ξ ∈ X, pm σ ξ ∈ X := by
    intro σ ξ hξ
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hξ
    rw [← hQpm]
    exact Submodule.mem_map_of_mem (hpmY σ y hy)
  have hXOm : ∀ j : Fin m, ∀ ξ ∈ X, Om F1 j ξ ∈ X := by
    intro j ξ hξ
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hξ
    rw [← hQOm]
    exact Submodule.mem_map_of_mem (hOmY j y hy)
  have hXtE : ∀ a b : Fin n, ∀ ξ ∈ X, tE Finset.univ (fun a b => F1 a b + -F2 b a) a b ξ = if a = b then c' • ξ else 0 := by
    intro a b ξ hξ
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hξ
    exact hQtE y hy a b
  obtain ⟨-, -, -, hgl2, hch2⟩ := hQ n M0 F2 hF2
  have hcomm12 : ∀ a b c d : Fin n, Commute (F1 a b) (-F2 d c) := fun a b c d => (hc a b d c).neg_right
  obtain ⟨-, hwall⟩ := hW n M0 F1 (fun a b => -F2 b a) hF1 hgl2 hcomm12 s (-((n : ℂ) - 1) - s) c' hs1 (hch2 _ hs2) m X hXne hXpm hXOm hXtE
  obtain ⟨hnm, ξ, hξX, hξalt⟩ := hwall hm
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hξX
  have hQalt : Q (alt (firstG m n) y) = alt (firstG m n) (Q y) := by
    simp only [alt, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul, hQpm]
  let ζ' : TV n M (Fin m) := alt (firstG m n) y
  have hζ'Y : ζ' ∈ Y := by
    show (∑ σ ∈ firstG m n, ((Equiv.Perm.sign σ : ℤ) : ℂ) • pm σ) y ∈ Y
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ (fun σ _ => Submodule.smul_mem _ _ (hpmY σ y hy))
  have hanti : ∀ τ ∈ firstG m n, pm τ ζ' = ((Equiv.Perm.sign τ : ℤ) : ℂ) • ζ' := fun τ hτ => pm_alt_firstG τ hτ y
  have hnz : ∃ I, q (ζ' I) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hξalt
    rw [← hQalt]
    funext I
    rw [hQap]
    exact hcon I
  set e := splitE m n hnm with he
  let g : TV n M (Fin (m - n) ⊕ Fin n) := reIx e ζ'
  let F : TV n (TV n M (Fin (m - n))) (Fin n) := cur g
  have hFanti : ∀ σ : Equiv.Perm (Fin n), pm σ F = ((Equiv.Perm.sign σ : ℤ) : ℂ) • F := cur_anti hnm ζ' hanti
  refine ⟨m - n, by omega, F id, fun γ => ?_, ?_⟩
  · have h1 : actT (fun _ : Fin (m - n) ⊕ Fin n => τ0) κ ρ γ g = χ γ • g := by
      have h0 := actT_reIx e (fun _ : Fin m => τ0) κ ρ γ ζ'
      rw [(hY ζ').1 hζ'Y γ, reIx_smul] at h0
      exact h0
    have h2 : (fun _ : Fin (m - n) ⊕ Fin n => τ0) = Sum.elim (fun _ : Fin (m - n) => τ0) (fun _ : Fin n => τ0) := by
      funext x
      cases x <;> rfl
    have h3 : actT (fun _ : Fin n => τ0) κ (actT (fun _ : Fin (m - n) => τ0) κ ρ) γ F = χ γ • F := by
      apply unc_inj
      rw [← actT_unc, unc_smul, unc_cur, ← h2, h1]
    have h4 := actT_anti_id τ0 κ (actT (fun _ : Fin (m - n) => τ0) κ ρ) γ F hFanti
    rw [h3] at h4
    have hdet := det_ne hK τ0 γ
    rw [prod_update_zpow (fun τ => (κ τ γ).det) c τ0 hdet, mul_smul]
    have h5 := congrArg (fun v => ((κ τ0 γ).det)⁻¹ • v) h4
    simp only [smul_smul, inv_mul_cancel₀ hdet, one_smul, Pi.smul_apply] at h5
    rw [← h5, smul_smul]
  · obtain ⟨I, hI⟩ := hnz
    let K : Fin (m - n) → Fin n := fun k => I (e.symm (Sum.inl k))
    let J : Fin n → Fin n := fun j => I (e.symm (Sum.inr j))
    obtain ⟨a, ha⟩ := anti_span F hFanti J
    refine ⟨K, fun hK0 => hI ?_⟩
    have hIe : Sum.elim K J ∘ e = I := by
      funext x
      simp only [Function.comp_apply]
      generalize hy : e x = w
      cases w with
      | inl k =>
        show I (e.symm (Sum.inl k)) = I x
        rw [← hy, Equiv.symm_apply_apply]
      | inr k =>
        show I (e.symm (Sum.inr k)) = I x
        rw [← hy, Equiv.symm_apply_apply]
    have h6 : ζ' I = F J K := by
      show ζ' I = ζ' (Sum.elim K J ∘ e)
      rw [hIe]
    rw [h6, ha, Pi.smul_apply, map_smul, hK0, smul_zero]

end PositivityTheory.Rg.Cz.CtrX

end
