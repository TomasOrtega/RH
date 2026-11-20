import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.ValAt

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

/- English proof (translation)
Introduce `v' hv'`. Rewrite using `[Subgroup.coe_mul, map_mul, h v' hv', h' v' hv', one_mul]`.
-/
theorem atV_mul {v : HeightOneSpectrum (𝓞 F)} {η η' : GA σ J} (h : AtV v η) (h' : AtV v η') : AtV v (η * η') := by
  intro v' hv'
  rw [Subgroup.coe_mul, map_mul, h v' hv', h' v' hv', one_mul]

/- English proof (translation)
Introduce `v' hv'`. Rewrite using `[Subgroup.coe_inv, map_inv, h v' hv', inv_one]`.
-/
theorem atV_inv {v : HeightOneSpectrum (𝓞 F)} {η : GA σ J} (h : AtV v η) : AtV v η⁻¹ := by
  intro v' hv'
  rw [Subgroup.coe_inv, map_inv, h v' hv', inv_one]

/- English proof (translation)
Establish `hm : κ.1 ∈ S.U`. Use `(S.U_eq _).2 ⟨κ.2, fun v' => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : v' = v`. Substitute `h` using the available equality. Conclude with `hU`.

Rewrite using `[hκ v' h]`. Conclude with `Subgroup.one_mem _`. Establish `hc : S.chi ⟨κ.1, hm⟩ = 1` using `S.chi_triv _ (fun v' hv' => hκ v' (fun h => hb (h ▸ hv')))`. Use function extensionality and compare the values at `y`. Use `hg 1 (Subgroup.one_mem _) x (x * κ) ⟨κ.1, hm⟩ (by rw [map_one, one_mul]; rfl) y y (fun τ => by simp [atInf])` as an intermediate fact.

Rewrite using `[this, hc, Units.val_one, one_mul]`.
-/
theorem inv_loc {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hb : v ∉ bad) (g) (hg : g ∈ AdFun S emb) (x κ : GA σ J) (hκ : AtV v κ)
    (hU : bc (prV (E := E) v) κ.1 ∈ S.Uloc v) : g (x * κ) = g x := by
  have hm : κ.1 ∈ S.U := by
    refine (S.U_eq _).2 ⟨κ.2, fun v' => ?_⟩
    by_cases h : v' = v
    · subst h; exact hU
    · rw [hκ v' h]; exact Subgroup.one_mem _
  have hc : S.chi ⟨κ.1, hm⟩ = 1 := S.chi_triv _ (fun v' hv' => hκ v' (fun h => hb (h ▸ hv')))
  funext y
  have := hg 1 (Subgroup.one_mem _) x (x * κ) ⟨κ.1, hm⟩ (by rw [map_one, one_mul]; rfl) y y
    (fun τ => by simp [atInf])
  rw [this, hc, Units.val_one, one_mul]

/- English proof (translation)
Establish `h : ∃ η', AtV v η' ∧ p (x * η') = p (x * η)` using `⟨η, hη, rfl⟩`. Unfold `valAt`. Rewrite using `[dif_pos h]`. Take `⟨h1, h2⟩` from `h.choose_spec`. Generalize the expression as in `h.choose = η0 at h1 h2`.

Establish `e : x * η = x * η0 * (η0⁻¹ * η)` using `by group`. Rewrite using `[e]`. Use `(inv_loc S emb v hb g hg _ _ (atV_mul (atV_inv h1) hη) ?_).symm` and prove the remaining obligations. Conclude with `(hp.2.1 (x * η0) _).1 (by rw [← e, h2])`.
-/
theorem val_self {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : Type} [Field k]
    (p : GA σ J → Pr (𝓞 E) (Fin n → E) k) (hb : v ∉ bad) (hp : PMap S v hv p) (g) (hg : g ∈ AdFun S emb)
    (x η : GA σ J) (hη : AtV v η) : valAt v p g x (p (x * η)) = g (x * η) := by
  have h : ∃ η', AtV v η' ∧ p (x * η') = p (x * η) := ⟨η, hη, rfl⟩
  unfold valAt
  rw [dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  generalize h.choose = η0 at h1 h2
  have e : x * η = x * η0 * (η0⁻¹ * η) := by group
  rw [e]
  refine (inv_loc S emb v hb g hg _ _ (atV_mul (atV_inv h1) hη) ?_).symm
  exact (hp.2.1 (x * η0) _).1 (by rw [← e, h2])

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J T f bad ι _ S emb v hv k _ p hb hp g hg`. Establish `key` using `val_self S emb v hv p hb hp g hg`. Use `⟨key, fun x η hη => ?_, fun a δ x q ha hδ => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Distinguish the cases in `h : ∃ η', AtV v η' ∧ p (x * η * η') = q`.

Take `⟨η', h1, rfl⟩` from `h`. Rewrite using `[key _ _ h1, mul_assoc, key _ _ (atV_mul hη h1)]`. Establish `h' : ¬ ∃ η', AtV v η' ∧ p (x * η') = q`. Introduce and unpack `⟨η', h1, h2⟩`. Use `h ⟨η⁻¹ * η', atV_mul (atV_inv hη) h1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← h2]`. Use `congr 1`. Use `group`. Unfold `valAt`. Rewrite using `[dif_neg h, dif_neg h']`.

Establish `hδv : AtV v δ` using `hδ.1`. Distinguish the cases in `h : ∃ η', AtV v η' ∧ p (x * η') = q`. Establish `hR : valAt v p (fun y => g (y * δ)) x q = g (x * h.choose * δ)`. Unfold `valAt`. Rewrite using `[dif_pos h]`.

Take `⟨h1, h2⟩` from `h.choose_spec`. Rewrite using `[hR]`. Generalize the expression as in `h.choose = η0 at h1 h2`. Rewrite using `[← h2, ← hp.2.2 _ δ a hδ, mul_assoc, key _ _ (atV_mul h1 hδv)]`. Establish `h' : ¬ ∃ η', AtV v η' ∧ p (x * η') = q.dil (a : k)`.

Introduce and unpack `⟨η', h1, h2⟩`. Use `h ⟨η' * δ⁻¹, atV_mul h1 (atV_inv hδv), ?_⟩` and prove the remaining obligations. Establish `h3` using `hp.2.2 (x * (η' * δ⁻¹)) δ a hδ`. Establish `e : x * (η' * δ⁻¹) * δ = x * η'` using `by group`. Rewrite `h3` using `[e, h2]`.

Establish `h4` using `congrArg (Pr.dil (a : k)⁻¹) h3`. Rewrite `h4` using `[Pr.dil_dil, Pr.dil_dil, inv_mul_cancel₀ ha, Pr.dil_one, Pr.dil_one]`. Conclude with `h4.symm`. Unfold `valAt`. Rewrite using `[dif_neg h, dif_neg h']`.
-/
theorem valAt_spec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ g ∈ AdFun S emb, (∀ x η : GA σ J, AtV v η → valAt v p g x (p (x * η)) = g (x * η)) ∧ (∀ x η : GA σ J, AtV v η → valAt v p g (x * η) = valAt v p g x) ∧ ∀ (a : ℤ) (δ x : GA σ J) (q : Pr (𝓞 E) (Fin n → E) k), (a : k) ≠ 0 → IsDia S v hv a δ → valAt v p g x (q.dil (a : k)) = valAt v p (fun y => g (y * δ)) x q := by
  intro F E _ _ _ _ _ σ n J T f bad ι _ S emb v hv k _ p hb hp g hg
  have key := val_self S emb v hv p hb hp g hg
  refine ⟨key, fun x η hη => ?_, fun a δ x q ha hδ => ?_⟩
  · funext q
    by_cases h : ∃ η', AtV v η' ∧ p (x * η * η') = q
    · obtain ⟨η', h1, rfl⟩ := h
      rw [key _ _ h1, mul_assoc, key _ _ (atV_mul hη h1)]
    · have h' : ¬ ∃ η', AtV v η' ∧ p (x * η') = q := by
        rintro ⟨η', h1, h2⟩
        refine h ⟨η⁻¹ * η', atV_mul (atV_inv hη) h1, ?_⟩
        rw [← h2]; congr 1; group
      unfold valAt
      rw [dif_neg h, dif_neg h']
  · have hδv : AtV v δ := hδ.1
    by_cases h : ∃ η', AtV v η' ∧ p (x * η') = q
    · have hR : valAt v p (fun y => g (y * δ)) x q = g (x * h.choose * δ) := by
        unfold valAt
        rw [dif_pos h]
      obtain ⟨h1, h2⟩ := h.choose_spec
      rw [hR]
      generalize h.choose = η0 at h1 h2
      rw [← h2, ← hp.2.2 _ δ a hδ, mul_assoc, key _ _ (atV_mul h1 hδv)]
    · have h' : ¬ ∃ η', AtV v η' ∧ p (x * η') = q.dil (a : k) := by
        rintro ⟨η', h1, h2⟩
        refine h ⟨η' * δ⁻¹, atV_mul h1 (atV_inv hδv), ?_⟩
        have h3 := hp.2.2 (x * (η' * δ⁻¹)) δ a hδ
        have e : x * (η' * δ⁻¹) * δ = x * η' := by group
        rw [e, h2] at h3
        have h4 := congrArg (Pr.dil (a : k)⁻¹) h3
        rw [Pr.dil_dil, Pr.dil_dil, inv_mul_cancel₀ ha, Pr.dil_one, Pr.dil_one] at h4
        exact h4.symm
      unfold valAt
      rw [dif_neg h, dif_neg h']

end GlobalTheory.LevelHecke.ValAt
