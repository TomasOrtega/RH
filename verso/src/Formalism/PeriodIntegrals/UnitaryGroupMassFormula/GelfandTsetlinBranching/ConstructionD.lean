import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

/- English proof (translation)
Introduce `i j hij`. Conclude with `Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)`.
-/
theorem natW_anti_D {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)

/- English proof (translation)
The claim follows from `Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl mu.natW (natW_anti_D mu)`.
-/
theorem extremal_mem_D (n : ℕ) (mu : DomWeight n) : extremal ℂ n mu ∈ nablaSq ℂ n mu :=
  Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl mu.natW (natW_anti_D mu)

/- English proof (translation)
The claim follows from `Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl mu.natW`.
-/
theorem extremal_ne_D (n : ℕ) (mu : DomWeight n) : extremal ℂ n mu ≠ 0 :=
  Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl mu.natW

def sqLinD (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ) :
    MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ where
  toFun := sqAct ℂ N lam g
  map_add' x y := by simp only [sqAct, map_add, smul_add]
  map_smul' c x := by
    simp only [sqAct, RingHom.id_apply, map_smul]
    rw [smul_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sqLinD_apply (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqLinD N lam g f = sqAct ℂ N lam g f := rfl

/- English proof (translation)
Use `⟨fun s _ => by` and prove the remaining obligations. Simplify using `only [LinearMap.zero_apply]`. Conclude with `Submodule.zero_mem _, fun g s _ => ?_⟩`. Simplify using `only [LinearMap.zero_apply]`. Rewrite using `[← sqLinD_apply, map_zero]`.
-/
theorem isEqv_zero_D {n N : ℕ} (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N) :
    IsEqv h mu lam 0 := by
  refine ⟨fun s _ => by
    simp only [LinearMap.zero_apply]
    exact Submodule.zero_mem _, fun g s _ => ?_⟩
  simp only [LinearMap.zero_apply]
  rw [← sqLinD_apply, map_zero]

/- English proof (translation)
Use `⟨fun s hs => ?_, fun g s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply]`. Conclude with `Submodule.smul_mem _ c (hφ.1 s hs)`. Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, hφ.2 g s hs, ← sqLinD_apply, ← sqLinD_apply, map_smul]`.
-/
theorem isEqv_smul_D {n N : ℕ} (h : n + 1 = N) {mu : DomWeight n} {lam : DomWeight N}
    {φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ} (hφ : IsEqv h mu lam φ) (c : ℂ) :
    IsEqv h mu lam (c • φ) := by
  refine ⟨fun s hs => ?_, fun g s hs => ?_⟩
  · rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ c (hφ.1 s hs)
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hφ.2 g s hs, ← sqLinD_apply, ← sqLinD_apply, map_smul]

/- English proof (translation)
Set `U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ)` to `nablaSq ℂ n mu ⊓ LinearMap.ker (φ - ψ)`. Establish `hU : U ≤ nablaSq ℂ n mu` using `inf_le_left`. Establish `hstab : ∀ (g : GL (Fin n) ℂ), ∀ f ∈ U, sqAct ℂ n mu g f ∈ U`. Introduce and unpack `g f ⟨hf1, hf2⟩`. Use `⟨(he n mu).2.2 g f hf1, ?_⟩` and prove the remaining obligations.

Establish `hf2' : φ f = ψ f`. Rewrite `hf2` using `[SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Conclude with `hf2`. Use `show sqAct ℂ n mu g f ∈ LinearMap.ker (φ - ψ)`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hφ.2 g f hf1, hψ.2 g f hf1, hf2']`.

Break down `(hI n mu).2.1 U hU hstab with hbot | htop` into its components or cases. It suffices to derive a contradiction. Establish `he_mem : extremal ℂ n mu ∈ U` using `⟨extremal_mem_D n mu, by show extremal ℂ n mu ∈ LinearMap.ker (φ - ψ)`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, hext, sub_self]⟩`. Rewrite `he_mem` using `[hbot]`.

Conclude with `extremal_ne_D n mu ((Submodule.mem_bot ℂ).mp he_mem)`. Introduce `s hs`. Establish `hsU : s ∈ U` using `by rw [htop]; exact hs`. Establish `h2 : s ∈ LinearMap.ker (φ - ψ)` using `hsU.2`. Rewrite `h2` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`.

Conclude with `h2`.
-/
theorem eq_on_of_extremal_D (hI : PI.HwIrred) (he : ExtremalFacts) {n N : ℕ} (h : n + 1 = N)
    {mu : DomWeight n} {lam : DomWeight N}
    {φ ψ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ}
    (hφ : IsEqv h mu lam φ) (hψ : IsEqv h mu lam ψ)
    (hext : φ (extremal ℂ n mu) = ψ (extremal ℂ n mu)) : ∀ s ∈ nablaSq ℂ n mu, φ s = ψ s := by
  let U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) := nablaSq ℂ n mu ⊓ LinearMap.ker (φ - ψ)
  have hU : U ≤ nablaSq ℂ n mu := inf_le_left
  have hstab : ∀ (g : GL (Fin n) ℂ), ∀ f ∈ U, sqAct ℂ n mu g f ∈ U := by
    rintro g f ⟨hf1, hf2⟩
    refine ⟨(he n mu).2.2 g f hf1, ?_⟩
    have hf2' : φ f = ψ f := by
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hf2
      exact hf2
    show sqAct ℂ n mu g f ∈ LinearMap.ker (φ - ψ)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hφ.2 g f hf1, hψ.2 g f hf1, hf2']
  rcases (hI n mu).2.1 U hU hstab with hbot | htop
  · exfalso
    have he_mem : extremal ℂ n mu ∈ U :=
      ⟨extremal_mem_D n mu, by
        show extremal ℂ n mu ∈ LinearMap.ker (φ - ψ)
        rw [LinearMap.mem_ker, LinearMap.sub_apply, hext, sub_self]⟩
    rw [hbot] at he_mem
    exact extremal_ne_D n mu ((Submodule.mem_bot ℂ).mp he_mem)
  · intro s hs
    have hsU : s ∈ U := by rw [htop]; exact hs
    have h2 : s ∈ LinearMap.ker (φ - ψ) := hsU.2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h2
    exact h2

/- English proof (translation)
Establish `hmem` using `extremal_mem_D n mu`. Use `⟨fun g hg1 hg2 => ?_, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ.2 g _ hmem, (he n mu).1 g hg1 hg2]`. Rewrite using `[← hφ.2 _ _ hmem, (he n mu).2.1 t, map_smul]`.
-/
theorem fixed_of_eqv_D (he : ExtremalFacts) {n N : ℕ} (h : n + 1 = N) {mu : DomWeight n} {lam : DomWeight N}
    {φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ} (hφ : IsEqv h mu lam φ) :
    IsFixedW h lam mu (φ (extremal ℂ n mu)) := by
  have hmem := extremal_mem_D n mu
  refine ⟨fun g hg1 hg2 => ?_, fun t => ?_⟩
  · rw [← hφ.2 g _ hmem, (he n mu).1 g hg1 hg2]
  · rw [← hφ.2 _ _ hmem, (he n mu).2.1 t, map_smul]

/- English proof (translation)
Establish `hmem` using `extremal_mem_D n mu`. Establish `hne' : φ' (extremal ℂ n mu) ≠ 0`. Introduce `h0`. Take `⟨s, hs, hs0⟩` from `hne`. Apply `hs0` to reduce the goal to its premises.

Establish `h3` using `eq_on_of_extremal_D hI he h hφ' (isEqv_zero_D h mu lam) (by rw [h0, LinearMap.zero_apply]) s hs`. Rewrite using `[h3, LinearMap.zero_apply]`. Take `⟨⟨c, hc⟩, hint⟩` from `ha n N h lam mu (φ (extremal ℂ n mu)) (φ' (extremal ℂ n mu)) (hφ.1 _ hmem) (hφ'.1 _ hmem) (fixed_of_eqv_D he h hφ) (fixed_of_eqv_D he h hφ') hne'`. Use `⟨hint, c, fun s hs => ?_⟩` and prove the remaining obligations. Establish `h3` using `eq_on_of_extremal_D hI he h hφ (isEqv_smul_D h hφ' c) (by rw [LinearMap.smul_apply, hc]) s hs`.

Rewrite using `[h3, LinearMap.smul_apply]`.
-/
theorem equivariant_map_interlacing_unique (hI : PI.HwIrred) (he : ExtremalFacts) (ha : FixedLine) {n N : ℕ} (h : n + 1 = N)
    (lam : DomWeight N) (mu : DomWeight n)
    (φ φ' : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (hφ : IsEqv h mu lam φ) (hφ' : IsEqv h mu lam φ') (hne : ∃ s ∈ nablaSq ℂ n mu, φ' s ≠ 0) :
    Interlace h lam mu ∧ ∃ c : ℂ, ∀ s ∈ nablaSq ℂ n mu, φ s = c • φ' s := by
  have hmem := extremal_mem_D n mu
  have hne' : φ' (extremal ℂ n mu) ≠ 0 := by
    intro h0
    obtain ⟨s, hs, hs0⟩ := hne
    apply hs0
    have h3 := eq_on_of_extremal_D hI he h hφ' (isEqv_zero_D h mu lam) (by rw [h0, LinearMap.zero_apply]) s hs
    rw [h3, LinearMap.zero_apply]
  obtain ⟨⟨c, hc⟩, hint⟩ := ha n N h lam mu (φ (extremal ℂ n mu)) (φ' (extremal ℂ n mu)) (hφ.1 _ hmem)
    (hφ'.1 _ hmem) (fixed_of_eqv_D he h hφ) (fixed_of_eqv_D he h hφ') hne'
  refine ⟨hint, c, fun s hs => ?_⟩
  have h3 := eq_on_of_extremal_D hI he h hφ (isEqv_smul_D h hφ' c) (by rw [LinearMap.smul_apply, hc]) s hs
  rw [h3, LinearMap.smul_apply]

def brSupD {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  ⨆ (mu : DomWeight n) (_ : Interlace h lam mu)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (_ : IsEqv h mu lam φ), (nablaSq ℂ n mu).map φ

/- English proof (translation)
Establish `hmemS : ∀ (mu : DomWeight n) (hint : Interlace h lam mu) (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ), (nablaSq ℂ n mu).map φ ≤ brSupD h lam` using `fun mu hint φ hφ => le_iSup_of_le mu (le_iSup_of_le hint (le_iSup_of_le φ (le_iSup_of_le hφ le_rfl)))`. Establish `hle : brSupD h lam ≤ nablaSq ℂ N lam`. Use `iSup_le fun mu => iSup_le fun hint => iSup_le fun φ => iSup_le fun hφ => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Conclude with `hφ.1 s hs`.

Establish `hstab : IsStable h lam (brSupD h lam)`. Introduce `g`. Establish `key : brSupD h lam ≤ (brSupD h lam).comap (sqLinD N lam (embGL ℂ n N h g))`. Use `iSup_le fun mu => iSup_le fun hint => iSup_le fun φ => iSup_le fun hφ => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨s, hs, rfl⟩`.

Rewrite using `[Submodule.mem_comap, sqLinD_apply, ← hφ.2 g s hs]`. Conclude with `hmemS mu hint φ hφ ⟨_, (he n mu).2.2 g s hs, rfl⟩`. Introduce `f hf`. Conclude with `key hf`. Take `⟨W', hW'le, hW'st, hsup, hinf⟩` from `hb n N h lam (brSupD h lam) hle hstab`.

Distinguish the cases in `hW' : W' = ⊥`. Rewrite `hsup` using `[hW', sup_bot_eq]`. Conclude with `hsup.symm`. It suffices to derive a contradiction. Take `⟨f, hfW, hf0, mu, hfix⟩` from `hc n N h lam W' hW'le hW'st hW'`.

Take `⟨φ, hφ, hφe⟩` from `hd n N h lam mu f (hW'le hfW) hfix hf0`. Establish `hint : Interlace h lam mu` using `(ha n N h lam mu f f (hW'le hfW) (hW'le hfW) hfix hfix hf0).2`. Establish `hfS : f ∈ brSupD h lam` using `hmemS mu hint φ hφ ⟨_, extremal_mem_D n mu, hφe⟩`. Establish `hfI : f ∈ brSupD h lam ⊓ W'` using `⟨hfS, hfW⟩`. Rewrite `hfI` using `[hinf]`.

Conclude with `hf0 ((Submodule.mem_bot ℂ).mp hfI)`.
-/
theorem branching_rule_decomposition (he : ExtremalFacts) (ha : FixedLine) (hb : StableCompl) (hc : HighestVec) (hd : Realize)
    {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) : nablaSq ℂ N lam = brSupD h lam := by
  have hmemS : ∀ (mu : DomWeight n) (hint : Interlace h lam mu)
      (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ),
      (nablaSq ℂ n mu).map φ ≤ brSupD h lam :=
    fun mu hint φ hφ => le_iSup_of_le mu (le_iSup_of_le hint (le_iSup_of_le φ (le_iSup_of_le hφ le_rfl)))
  have hle : brSupD h lam ≤ nablaSq ℂ N lam := by
    refine iSup_le fun mu => iSup_le fun hint => iSup_le fun φ => iSup_le fun hφ => ?_
    rintro _ ⟨s, hs, rfl⟩
    exact hφ.1 s hs
  have hstab : IsStable h lam (brSupD h lam) := by
    intro g
    have key : brSupD h lam ≤ (brSupD h lam).comap (sqLinD N lam (embGL ℂ n N h g)) := by
      refine iSup_le fun mu => iSup_le fun hint => iSup_le fun φ => iSup_le fun hφ => ?_
      rintro _ ⟨s, hs, rfl⟩
      rw [Submodule.mem_comap, sqLinD_apply, ← hφ.2 g s hs]
      exact hmemS mu hint φ hφ ⟨_, (he n mu).2.2 g s hs, rfl⟩
    intro f hf
    exact key hf
  obtain ⟨W', hW'le, hW'st, hsup, hinf⟩ := hb n N h lam (brSupD h lam) hle hstab
  by_cases hW' : W' = ⊥
  · rw [hW', sup_bot_eq] at hsup
    exact hsup.symm
  · exfalso
    obtain ⟨f, hfW, hf0, mu, hfix⟩ := hc n N h lam W' hW'le hW'st hW'
    obtain ⟨φ, hφ, hφe⟩ := hd n N h lam mu f (hW'le hfW) hfix hf0
    have hint : Interlace h lam mu := (ha n N h lam mu f f (hW'le hfW) (hW'le hfW) hfix hfix hf0).2
    have hfS : f ∈ brSupD h lam := hmemS mu hint φ hφ ⟨_, extremal_mem_D n mu, hφe⟩
    have hfI : f ∈ brSupD h lam ⊓ W' := ⟨hfS, hfW⟩
    rw [hinf] at hfI
    exact hf0 ((Submodule.mem_bot ℂ).mp hfI)

/- English proof (translation)
Introduce `n N hnN lam`. Use `⟨fun mu φ φ' hψ hne => ?_, branching_rule_decomposition he ha hb hc hd hnN lam⟩` and prove the remaining obligations. Establish `hφ : IsEqv hnN mu lam φ` using `hψ φ (by simp)`. Establish `hφ' : IsEqv hnN mu lam φ'` using `hψ φ' (by simp)`. Conclude with `equivariant_map_interlacing_unique h he ha hnN lam mu φ φ' hφ hφ' hne`.
-/
theorem gTBranch_of_steps (h : PI.HwIrred) (he : ExtremalFacts) (ha : FixedLine) (hb : StableCompl)
    (hc : HighestVec) (hd : Realize) : PI.GTBranch := by
  intro n N hnN lam
  refine ⟨fun mu φ φ' hψ hne => ?_, branching_rule_decomposition he ha hb hc hd hnN lam⟩
  have hφ : IsEqv hnN mu lam φ := hψ φ (by simp)
  have hφ' : IsEqv hnN mu lam φ' := hψ φ' (by simp)
  exact equivariant_map_interlacing_unique h he ha hnN lam mu φ φ' hφ hφ' hne

end PI.WGB
