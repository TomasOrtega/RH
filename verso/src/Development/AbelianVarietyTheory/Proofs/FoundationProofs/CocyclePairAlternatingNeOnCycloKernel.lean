import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.PairSpan

section Abstract

variable {Γ k : Type} [Group Γ] [Field k]

/- English proof (translation)
Distinguish the cases in `h0 : v 0 = 0`. Establish `h1 : v 1 ≠ 0`. Apply the tactic sequence `intro h1; apply hv; funext i; fin_cases i <;> simp [h0, h1]`. Conclude with `⟨![1, 0], by simp [h1]⟩`. Conclude with `⟨![0, 1], by simp [h0]⟩`.
-/
theorem alt_left_nondeg {v : Fin 2 → k} (hv : v ≠ 0) : ∃ a : Fin 2 → k, v 0 * a 1 - v 1 * a 0 ≠ 0 := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; apply hv; funext i; fin_cases i <;> simp [h0, h1]
    exact ⟨![1, 0], by simp [h1]⟩
  · exact ⟨![0, 1], by simp [h0]⟩

/- English proof (translation)
The claim follows from `hirr.2.2 U le_top (by intro g v hv; exact hU g g.2 v hv)`.
-/
theorem stable_cases {W : Γ →* GL (Fin 2) k} {H : Subgroup Γ} (hirr : UpperTheory.V.Af.IsIrr (W.comp H.subtype))
    (U : Submodule k (Fin 2 → k)) (hU : ∀ s ∈ H, ∀ v ∈ U, (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ U) :
    U = ⊥ ∨ U = ⊤ :=
  hirr.2.2 U le_top (by intro g v hv; exact hU g g.2 v hv)

/- English proof (translation)
Establish `h1 : y 1 = 0` using `by simpa using hy 1 1`. Establish `h2 : y s + (ρ s : Matrix (Fin n) (Fin n) k) *ᵥ y s⁻¹ = 0` using `by rw [← hy, mul_inv_cancel, h1]`. Rewrite using `[hy, hy, map_mul, hg, mul_one, add_right_comm, h2, zero_add]`.
-/
theorem coc_conj {n : ℕ} (ρ : Γ →* GL (Fin n) k) (y : Γ → Fin n → k)
    (hy : ∀ g h, y (g * h) = y g + (ρ g : Matrix (Fin n) (Fin n) k) *ᵥ y h) (s g : Γ) (hg : ρ g = 1) :
    y (s * g * s⁻¹) = (ρ s : Matrix (Fin n) (Fin n) k) *ᵥ y g := by
  have h1 : y 1 = 0 := by simpa using hy 1 1
  have h2 : y s + (ρ s : Matrix (Fin n) (Fin n) k) *ᵥ y s⁻¹ = 0 := by rw [← hy, mul_inv_cancel, h1]
  rw [hy, hy, map_mul, hg, mul_one, add_right_comm, h2, zero_add]

end Abstract
end GlobalTheory.Ord2.PairSpan

namespace GlobalTheory.Ord2.PairSpan

variable {Γ k : Type} [Group Γ] [Field k]

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Set `Sig : Submodule k ((Fin 2 → k) × (Fin 2 → k))` to `Submodule.span k ((fun g => (y g, z g)) '' N)`. Establish `hgen : ∀ g ∈ N, (y g, z g) ∈ Sig` using `fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩`. Establish `hinv : ∀ s ∈ H, ∀ σ ∈ Sig, ((W s : Matrix (Fin 2) (Fin 2) k) *ᵥ σ.1, (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ σ.2) ∈ Sig`.

Introduce `s hs σ hσ`. Proceed by induction on `hσ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, hg, rfl⟩` from `hx`. Rewrite using `[← hy s hs g hg, ← hz s hs g hg]`.

Conclude with `hgen _ (hN s hs g hg)`. Consider the case `zero`. Simplify using `only [Prod.fst_zero, Prod.snd_zero, Matrix.mulVec_zero, Prod.mk_zero_zero]`. Conclude with `Sig.zero_mem`. Consider the case `add x x' _ _ ihx ihx' => simpa [Matrix.mulVec_add] using Sig.add_mem ihx ihx'`.

Consider the case `smul a x _ ihx => simpa [Matrix.mulVec_smul] using Sig.smul_mem a ihx`. Establish `hB : ∀ g ∈ N, ∀ σ ∈ Sig, y g 0 * σ.2 1 - y g 1 * σ.2 0 = σ.1 0 * z g 1 - σ.1 1 * z g 0`. Introduce `g hg σ hσ`. Proceed by induction on `hσ using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨h, hh, rfl⟩` from `hx`. Conclude with `(hcon g hg h hh).symm`. Consider the case `zero => simp`. Consider the case `add x x' _ _ ihx ihx'`. Simplify using `only [Prod.fst_add, Prod.snd_add, Pi.add_apply]`.

Take the linear combination `ihx + ihx'`. Consider the case `smul a x _ ihx`. Simplify using `only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]`. Take the linear combination `a * ihx`. Set `K' : Submodule k (Fin 2 → k)` to `Sig.comap (LinearMap.inr k (Fin 2 → k) (Fin 2 → k))`.

Establish `hK' : K' = ⊥`. Break down `stable_cases hirr K' (by` into its components or cases. Introduce `s hs v hv`. Use `hinv s hs _ hv` as an intermediate fact. Simplify `this) with h | h` using `[K', Matrix.mulVec_zero]`.

Conclude with `h`. It suffices to derive a contradiction. Take `⟨g, hg, hyg⟩` from `hy0`. Take `⟨a, ha⟩` from `alt_left_nondeg hyg`. Establish `hmem : ((0 : Fin 2 → k), a) ∈ Sig`.

Establish `: a ∈ K'` using `h ▸ Submodule.mem_top`. Simplify `this` using `[K']`. Conclude with `ha ((hB g hg _ hmem).trans (by simp))`. Set `P : Submodule k (Fin 2 → k)` to `Sig.map (LinearMap.fst k (Fin 2 → k) (Fin 2 → k))`. Establish `hP : P = ⊤`.

Break down `stable_cases hirr P (by` into its components or cases. Introduce and unpack `s hs v ⟨σ, hσ, rfl⟩`. Conclude with `⟨_, hinv s hs σ hσ, rfl⟩) with h | h`. It suffices to derive a contradiction. Take `⟨g, hg, hyg⟩` from `hy0`.

Establish `: y g ∈ P` using `⟨_, hgen g hg, rfl⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `hyg this`. Conclude with `h`. Set `f : Sig →ₗ[k] (Fin 2 → k)` to `(LinearMap.fst k (Fin 2 → k) (Fin 2 → k)).comp Sig.subtype`.

Establish `hfi : Function.Injective f`. Use `(injective_iff_map_eq_zero f).2 fun σ hσ => ?_` and prove the remaining obligations. Establish `h1 : (σ : (Fin 2 → k) × (Fin 2 → k)).1 = 0` using `hσ`. Establish `h2 : (σ : (Fin 2 → k) × (Fin 2 → k)).2 ∈ K'` using `by show LinearMap.inr k _ _ (σ : (Fin 2 → k) × (Fin 2 → k)).2 ∈ Sig`. Apply the tactic sequence `have : LinearMap.inr k (Fin 2 → k) (Fin 2 → k) (σ : (Fin 2 → k) × (Fin 2 → k)).2 = σ := by ext1 <;> simp [h1]`.

Rewrite using `[this]`. Conclude with `σ.2`. Rewrite `h2` using `[hK', Submodule.mem_bot]`. Conclude with `Subtype.ext (Prod.ext h1 h2)`. Establish `hfs : Function.Surjective f`.

Introduce `a`. Establish `: a ∈ P` using `hP ▸ Submodule.mem_top`. Take `⟨σ, hσ, rfl⟩` from `this`. Conclude with `⟨⟨σ, hσ⟩, rfl⟩`. Set `e` to `LinearEquiv.ofBijective f ⟨hfi, hfs⟩`.

Set `φ : Module.End k (Fin 2 → k)` to `(LinearMap.snd k (Fin 2 → k) (Fin 2 → k)).comp (Sig.subtype.comp e.symm.toLinearMap)`. Establish `hφmem : ∀ a, (a, φ a) ∈ Sig`. Introduce `a`. Establish `h1 : ((e.symm a : Sig) : (Fin 2 → k) × (Fin 2 → k)).1 = a` using `e.apply_symm_apply a`. Establish `: (a, φ a) = ((e.symm a : Sig) : (Fin 2 → k) × (Fin 2 → k))` using `Prod.ext h1.symm rfl`.

Rewrite using `[this]`. Conclude with `(e.symm a).2`. Establish `hφ : ∀ σ ∈ Sig, φ σ.1 = σ.2`. Introduce `σ hσ`. Establish `: e.symm σ.1 = ⟨σ, hσ⟩` using `e.symm_apply_eq.2 rfl`.

Use `show ((e.symm σ.1 : Sig) : (Fin 2 → k) × (Fin 2 → k)).2 = σ.2`. Rewrite using `[this]`. Establish `hφW : ∀ s ∈ H, ∀ a, φ ((W s : Matrix (Fin 2) (Fin 2) k) *ᵥ a) = (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ φ a` using `fun s hs a => hφ _ (hinv s hs _ (hφmem a))`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue φ`. Establish `hE : Module.End.eigenspace φ c = ⊤`.

Break down `stable_cases hirr (Module.End.eigenspace φ c) (by` into its components or cases. Introduce `s hs v hv`. Rewrite `hv`, the goal using `[Module.End.mem_eigenspace_iff]`. Rewrite using `[hφW s hs, hv, Matrix.mulVec_smul]) with h | h`. Conclude with `absurd h (Module.End.hasEigenvalue_iff.1 hc)`.

Conclude with `h`. Establish `hφc : ∀ a, φ a = c • a` using `fun a => Module.End.mem_eigenspace_iff.1 (hE ▸ Submodule.mem_top)`. Establish `hzy : ∀ g ∈ N, z g = c • y g` using `fun g hg => by rw [← hφc]; exact (hφ _ (hgen g hg)).symm`. Take `⟨g1, hg1, hzg1⟩` from `hz0`. Establish `hc0 : c ≠ 0` using `by rintro rfl; apply hzg1; rw [hzy g1 hg1, zero_smul]`.

Take `⟨g0, hg0, hyg0⟩` from `hy0`. Establish `horth : ∀ h ∈ N, y g0 0 * y h 1 - y g0 1 * y h 0 = 0`. Introduce `h hh`. Use `hcon h hh g0 hg0` as an intermediate fact. Rewrite `this` using `[hzy h hh, hzy g0 hg0]`.

Simplify using `only [Pi.smul_apply, smul_eq_mul] at this`. Establish `h2 : (2 * c) * (y g0 0 * y h 1 - y g0 1 * y h 0) = 0` using `by linear_combination this`. Break down `mul_eq_zero.1 h2 with h3 | h3` into its components or cases. Use the proof step `exfalso; exact hc0 (by simpa using h3)`. Conclude with `h3`.

Establish `hall : ∀ σ ∈ Sig, y g0 0 * σ.1 1 - y g0 1 * σ.1 0 = 0`. Introduce `σ hσ`. Proceed by induction on `hσ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨h, hh, rfl⟩` from `hx`.

Conclude with `horth h hh`. Consider the case `zero => simp`. Consider the case `add x x' _ _ ihx ihx'`. Simplify using `only [Prod.fst_add, Pi.add_apply]`. Take the linear combination `ihx + ihx'`.

Consider the case `smul a x _ ihx`. Simplify using `only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]`. Take the linear combination `a * ihx`. Take `⟨a, ha⟩` from `alt_left_nondeg hyg0`. Conclude with `ha (hall _ (hφmem a))`.
-/
theorem exists_pair_ne [IsAlgClosed k] [CharZero k] {W : Γ →* GL (Fin 2) k} {H : Subgroup Γ}
    (hirr : UpperTheory.V.Af.IsIrr (W.comp H.subtype)) {N : Set Γ}
    (hN : ∀ s ∈ H, ∀ g ∈ N, s * g * s⁻¹ ∈ N) {y z : Γ → Fin 2 → k}
    (hy : ∀ s ∈ H, ∀ g ∈ N, y (s * g * s⁻¹) = (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ y g)
    (hz : ∀ s ∈ H, ∀ g ∈ N, z (s * g * s⁻¹) = (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ z g)
    (hy0 : ∃ g ∈ N, y g ≠ 0) (hz0 : ∃ g ∈ N, z g ≠ 0) :
    ∃ g ∈ N, ∃ h ∈ N, y h 0 * z g 1 - y h 1 * z g 0 ≠ y g 0 * z h 1 - y g 1 * z h 0 := by
  by_contra hcon
  push_neg at hcon
  let Sig : Submodule k ((Fin 2 → k) × (Fin 2 → k)) := Submodule.span k ((fun g => (y g, z g)) '' N)
  have hgen : ∀ g ∈ N, (y g, z g) ∈ Sig := fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩
  have hinv : ∀ s ∈ H, ∀ σ ∈ Sig,
      ((W s : Matrix (Fin 2) (Fin 2) k) *ᵥ σ.1, (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ σ.2) ∈ Sig := by
    intro s hs σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      rw [← hy s hs g hg, ← hz s hs g hg]
      exact hgen _ (hN s hs g hg)
    | zero =>
      simp only [Prod.fst_zero, Prod.snd_zero, Matrix.mulVec_zero, Prod.mk_zero_zero]
      exact Sig.zero_mem
    | add x x' _ _ ihx ihx' => simpa [Matrix.mulVec_add] using Sig.add_mem ihx ihx'
    | smul a x _ ihx => simpa [Matrix.mulVec_smul] using Sig.smul_mem a ihx
  have hB : ∀ g ∈ N, ∀ σ ∈ Sig, y g 0 * σ.2 1 - y g 1 * σ.2 0 = σ.1 0 * z g 1 - σ.1 1 * z g 0 := by
    intro g hg σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      exact (hcon g hg h hh).symm
    | zero => simp
    | add x x' _ _ ihx ihx' =>
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      linear_combination ihx + ihx'
    | smul a x _ ihx =>
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      linear_combination a * ihx
  let K' : Submodule k (Fin 2 → k) := Sig.comap (LinearMap.inr k (Fin 2 → k) (Fin 2 → k))
  have hK' : K' = ⊥ := by
    rcases stable_cases hirr K' (by
      intro s hs v hv
      have := hinv s hs _ hv
      simpa [K', Matrix.mulVec_zero] using this) with h | h
    · exact h
    · exfalso
      obtain ⟨g, hg, hyg⟩ := hy0
      obtain ⟨a, ha⟩ := alt_left_nondeg hyg
      have hmem : ((0 : Fin 2 → k), a) ∈ Sig := by
        have : a ∈ K' := h ▸ Submodule.mem_top
        simpa [K'] using this
      exact ha ((hB g hg _ hmem).trans (by simp))
  let P : Submodule k (Fin 2 → k) := Sig.map (LinearMap.fst k (Fin 2 → k) (Fin 2 → k))
  have hP : P = ⊤ := by
    rcases stable_cases hirr P (by
      rintro s hs v ⟨σ, hσ, rfl⟩
      exact ⟨_, hinv s hs σ hσ, rfl⟩) with h | h
    · exfalso
      obtain ⟨g, hg, hyg⟩ := hy0
      have : y g ∈ P := ⟨_, hgen g hg, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hyg this
    · exact h
  let f : Sig →ₗ[k] (Fin 2 → k) := (LinearMap.fst k (Fin 2 → k) (Fin 2 → k)).comp Sig.subtype
  have hfi : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun σ hσ => ?_
    have h1 : (σ : (Fin 2 → k) × (Fin 2 → k)).1 = 0 := hσ
    have h2 : (σ : (Fin 2 → k) × (Fin 2 → k)).2 ∈ K' := by
      show LinearMap.inr k _ _ (σ : (Fin 2 → k) × (Fin 2 → k)).2 ∈ Sig
      have : LinearMap.inr k (Fin 2 → k) (Fin 2 → k) (σ : (Fin 2 → k) × (Fin 2 → k)).2 = σ := by
        ext1 <;> simp [h1]
      rw [this]; exact σ.2
    rw [hK', Submodule.mem_bot] at h2
    exact Subtype.ext (Prod.ext h1 h2)
  have hfs : Function.Surjective f := by
    intro a
    have : a ∈ P := hP ▸ Submodule.mem_top
    obtain ⟨σ, hσ, rfl⟩ := this
    exact ⟨⟨σ, hσ⟩, rfl⟩
  let e := LinearEquiv.ofBijective f ⟨hfi, hfs⟩
  let φ : Module.End k (Fin 2 → k) :=
    (LinearMap.snd k (Fin 2 → k) (Fin 2 → k)).comp (Sig.subtype.comp e.symm.toLinearMap)
  have hφmem : ∀ a, (a, φ a) ∈ Sig := by
    intro a
    have h1 : ((e.symm a : Sig) : (Fin 2 → k) × (Fin 2 → k)).1 = a := e.apply_symm_apply a
    have : (a, φ a) = ((e.symm a : Sig) : (Fin 2 → k) × (Fin 2 → k)) := Prod.ext h1.symm rfl
    rw [this]; exact (e.symm a).2
  have hφ : ∀ σ ∈ Sig, φ σ.1 = σ.2 := by
    intro σ hσ
    have : e.symm σ.1 = ⟨σ, hσ⟩ := e.symm_apply_eq.2 rfl
    show ((e.symm σ.1 : Sig) : (Fin 2 → k) × (Fin 2 → k)).2 = σ.2
    rw [this]
  have hφW : ∀ s ∈ H, ∀ a, φ ((W s : Matrix (Fin 2) (Fin 2) k) *ᵥ a) = (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ φ a :=
    fun s hs a => hφ _ (hinv s hs _ (hφmem a))
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue φ
  have hE : Module.End.eigenspace φ c = ⊤ := by
    rcases stable_cases hirr (Module.End.eigenspace φ c) (by
      intro s hs v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [hφW s hs, hv, Matrix.mulVec_smul]) with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
    · exact h
  have hφc : ∀ a, φ a = c • a := fun a => Module.End.mem_eigenspace_iff.1 (hE ▸ Submodule.mem_top)
  have hzy : ∀ g ∈ N, z g = c • y g := fun g hg => by rw [← hφc]; exact (hφ _ (hgen g hg)).symm
  obtain ⟨g1, hg1, hzg1⟩ := hz0
  have hc0 : c ≠ 0 := by rintro rfl; apply hzg1; rw [hzy g1 hg1, zero_smul]
  obtain ⟨g0, hg0, hyg0⟩ := hy0
  have horth : ∀ h ∈ N, y g0 0 * y h 1 - y g0 1 * y h 0 = 0 := by
    intro h hh
    have := hcon h hh g0 hg0
    rw [hzy h hh, hzy g0 hg0] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have h2 : (2 * c) * (y g0 0 * y h 1 - y g0 1 * y h 0) = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exfalso; exact hc0 (by simpa using h3)
    · exact h3
  have hall : ∀ σ ∈ Sig, y g0 0 * σ.1 1 - y g0 1 * σ.1 0 = 0 := by
    intro σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      exact horth h hh
    | zero => simp
    | add x x' _ _ ihx ihx' =>
      simp only [Prod.fst_add, Pi.add_apply]
      linear_combination ihx + ihx'
    | smul a x _ ihx =>
      simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      linear_combination a * ihx
  obtain ⟨a, ha⟩ := alt_left_nondeg hyg0
  exact ha (hall _ (hφmem a))

end GlobalTheory.Ord2.PairSpan

namespace GlobalTheory.Ord2

open PairSpan in

/- English proof (translation)
Introduce `l _ Ω _ _ _ e S A W hW y hyZ z hzZ hy0 hz0`. Establish `hy' : ∀ g h, y (g * h) = y g + (W g : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ y h` using `fun g h => by`. Rewrite using `[hyZ.2 g h]`. Both sides reduce to the same expression. Establish `hz' : ∀ g h, z (g * h) = z g + (dual1 W g : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ z h` using `fun g h => by`.

Rewrite using `[hzZ.2 g h]`. Both sides reduce to the same expression. Establish `hnorm : (N0g W).Normal` using `by unfold N0g; infer_instance`. Establish `hdual : ∀ s, cycBar ℚ Ω l s = 1 → dt W s = 1 → dual1 W s = W s`. Introduce `s h1 h2`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[dual1, tw_val]`. Simplify using `[h1, h2]`. Establish `hN1 : ∀ g ∈ N0g W, W g = 1` using `fun g hg => (Subgroup.mem_inf.1 hg).2`. Establish `hNd : ∀ g ∈ N0g W, dual1 W g = 1`.

Introduce `g hg`. Establish `h1 : cycBar ℚ Ω l g = 1` using `(Subgroup.mem_inf.1 hg).1`. Establish `h2 : dt W g = 1` using `by show Matrix.GeneralLinearGroup.det (W g) = 1`. Rewrite using `[hN1 g hg, map_one]`. Rewrite using `[hdual g h1 h2, hN1 g hg]`.

Establish `hH : ∀ s ∈ H0g W, dual1 W s = W s` using `fun s hs => hdual s (Subgroup.mem_inf.1 hs).1 (Subgroup.mem_inf.1 hs).2`. Take `⟨g, hg, h, hh, hne⟩` from `exists_pair_ne (k := Qbar l) (W := W) (H := H0g W) (N := (N0g W : Set (G ℚ Ω))) hW.irr (fun s _ g hg => hnorm.conj_mem g hg s) (y := y) (z := z) (fun s _ g hg => coc_conj W y hy' s g (hN1 g hg)) (fun s hs g hg => by rw [coc_conj (dual1 W) z hz' s g (hNd g hg), hH s hs]) hy0 hz0`. Conclude with `⟨g, hg, h, hh, hne⟩`.
-/
theorem exists_om_ne_swap_on_N0g : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ y ∈ Z1 (Loc.colRep W),
    ∀ z ∈ Z1 (Loc.colRep (dual1 W)), (∃ g ∈ N0g W, y g ≠ 0) → (∃ g ∈ N0g W, z g ≠ 0) →
    ∃ g ∈ N0g W, ∃ h ∈ N0g W, om (y h) (z g) ≠ om (y g) (z h) := by
  intro l _ Ω _ _ _ e S A W hW y hyZ z hzZ hy0 hz0
  have hy' : ∀ g h, y (g * h) = y g + (W g : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ y h := fun g h => by
    rw [hyZ.2 g h]; rfl
  have hz' : ∀ g h, z (g * h) = z g + (dual1 W g : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ z h := fun g h => by
    rw [hzZ.2 g h]; rfl
  have hnorm : (N0g W).Normal := by unfold N0g; infer_instance
  have hdual : ∀ s, cycBar ℚ Ω l s = 1 → dt W s = 1 → dual1 W s = W s := by
    intro s h1 h2
    apply Units.ext
    rw [dual1, tw_val]
    simp [h1, h2]
  have hN1 : ∀ g ∈ N0g W, W g = 1 := fun g hg => (Subgroup.mem_inf.1 hg).2
  have hNd : ∀ g ∈ N0g W, dual1 W g = 1 := by
    intro g hg
    have h1 : cycBar ℚ Ω l g = 1 := (Subgroup.mem_inf.1 hg).1
    have h2 : dt W g = 1 := by
      show Matrix.GeneralLinearGroup.det (W g) = 1
      rw [hN1 g hg, map_one]
    rw [hdual g h1 h2, hN1 g hg]
  have hH : ∀ s ∈ H0g W, dual1 W s = W s := fun s hs =>
    hdual s (Subgroup.mem_inf.1 hs).1 (Subgroup.mem_inf.1 hs).2
  obtain ⟨g, hg, h, hh, hne⟩ := exists_pair_ne (k := Qbar l) (W := W) (H := H0g W) (N := (N0g W : Set (G ℚ Ω)))
    hW.irr (fun s _ g hg => hnorm.conj_mem g hg s)
    (y := y) (z := z)
    (fun s _ g hg => coc_conj W y hy' s g (hN1 g hg))
    (fun s hs g hg => by rw [coc_conj (dual1 W) z hz' s g (hNd g hg), hH s hs])
    hy0 hz0
  exact ⟨g, hg, h, hh, hne⟩

end GlobalTheory.Ord2

end
