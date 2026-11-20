import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerMore

noncomputable section

namespace GlobalTheory.CocycleChar

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.InductiveNormBound.main`. Consider the case `exact _root_.GlobalTheory.InductiveNormBound.main`. Consider the case `(apply _root_.GlobalTheory.InductiveNormBound.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.InductiveNormBound.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.InductiveNormBound.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.InductiveNormBound.main ..)`.
-/
theorem pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.InductiveNormBound.main
  | exact _root_.GlobalTheory.InductiveNormBound.main
  | (apply _root_.GlobalTheory.InductiveNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.InductiveNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InductiveNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InductiveNormBound.main ..)

/- English proof (translation)
Introduce `A V _ _ _ _ _ _ _ _ lam hlam ε ⟨N, hN, hεN⟩ hε0 χ hχ hker hmul`. Establish `hχ0 : χ 0 = 1` using `hker 0 (map_zero lam)`. Establish `hW : lam ⁻¹' N ∩ {a : A | ‖χ a - 1‖ < 1 / 2} ∈ nhds (0 : A)`. Use `Filter.inter_mem ?_ ?_` and prove the remaining obligations. Conclude with `hlam.continuousAt.preimage_mem_nhds (by simpa using hN)`.

Conclude with `(isOpen_lt (hχ.sub continuous_const).norm continuous_const).mem_nhds (by simp [hχ0])`. Take `⟨K₀, hK₀⟩` from `NonarchimedeanAddGroup.is_nonarchimedean _ hW`. Establish `hpow : ∀ a ∈ K₀, ∀ n : ℕ, χ (n • a) = χ a ^ n`. Introduce `a ha n`. Proceed by induction on `n with`.

Consider the case `zero => simp [hχ0]`. Consider the case `succ n ih`. Establish `h1 : n • a ∈ K₀` using `K₀.toAddSubgroup.nsmul_mem ha n`. Rewrite using `[succ_nsmul, hmul, ih, hεN _ (hK₀ h1).1 _ (hK₀ ha).1, pow_succ, mul_one]`. Establish `hK₀one : ∀ a ∈ K₀, χ a = 1`.

Introduce `a ha`. Use `pow_near_one fun n => ?_` and prove the remaining obligations. Rewrite using `[← hpow a ha n]`. Conclude with `(hK₀ (K₀.toAddSubgroup.nsmul_mem ha n)).2`. Use `set S : AddSubgroup A := K₀.toAddSubgroup ⊔ lam.ker with hSdef`.

Establish `hSopen : IsOpen (S : Set A)` using `AddSubgroup.isOpen_mono (le_sup_left : K₀.toAddSubgroup ≤ S) K₀.isOpen`. Use `set C : Set A := (S : Set A)ᶜ`. Establish `hCc : IsCompact C` using `hSopen.isClosed_compl.isCompact`. Establish `hLc : IsClosed (lam '' C)` using `(hCc.image hlam).isClosed`. Establish `h0 : (0 : V) ∉ lam '' C`.

Introduce and unpack `⟨c, hc, hc0⟩`. Conclude with `hc (le_sup_right (a := K₀.toAddSubgroup) (AddMonoidHom.mem_ker.2 hc0))`. Use `⟨(lam '' C)ᶜ, hLc.isOpen_compl.mem_nhds h0, fun a ha => ?_⟩` and prove the remaining obligations. Establish `haS : a ∈ S`. Assume the negation of the conclusion as `h`.

Conclude with `ha ⟨a, h, rfl⟩`. Take `⟨k, hk, n, hn, rfl⟩` from `AddSubgroup.mem_sup.1 haS`. Rewrite `hn` using `[AddMonoidHom.mem_ker]`. Rewrite using `[hmul, hK₀one k hk, hker n hn, hn, hε0, mul_one, mul_one]`.
-/
theorem cocycle_char_trivial_near_zero :
    ∀ {A V : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A]
    [NonarchimedeanAddGroup A] [AddCommGroup V] [TopologicalSpace V] [T2Space V] (lam : A →+ V), Continuous lam →
    ∀ (ε : V → V → ℂ), (∃ N ∈ nhds (0 : V), ∀ x ∈ N, ∀ y ∈ N, ε x y = 1) → (∀ x, ε x 0 = 1) →
    ∀ (χ : A → ℂ), Continuous χ → (∀ a, lam a = 0 → χ a = 1) →
    (∀ a b, χ (a + b) = χ a * χ b * ε (lam a) (lam b)) → ∃ U ∈ nhds (0 : V), ∀ a, lam a ∈ U → χ a = 1 := by
  intro A V _ _ _ _ _ _ _ _ lam hlam ε ⟨N, hN, hεN⟩ hε0 χ hχ hker hmul
  have hχ0 : χ 0 = 1 := hker 0 (map_zero lam)

  have hW : lam ⁻¹' N ∩ {a : A | ‖χ a - 1‖ < 1 / 2} ∈ nhds (0 : A) := by
    refine Filter.inter_mem ?_ ?_
    · exact hlam.continuousAt.preimage_mem_nhds (by simpa using hN)
    · exact (isOpen_lt (hχ.sub continuous_const).norm continuous_const).mem_nhds (by simp [hχ0])
  obtain ⟨K₀, hK₀⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hW
  have hpow : ∀ a ∈ K₀, ∀ n : ℕ, χ (n • a) = χ a ^ n := by
    intro a ha n
    induction n with
    | zero => simp [hχ0]
    | succ n ih =>
      have h1 : n • a ∈ K₀ := K₀.toAddSubgroup.nsmul_mem ha n
      rw [succ_nsmul, hmul, ih, hεN _ (hK₀ h1).1 _ (hK₀ ha).1, pow_succ, mul_one]
  have hK₀one : ∀ a ∈ K₀, χ a = 1 := by
    intro a ha
    refine pow_near_one fun n => ?_
    rw [← hpow a ha n]
    exact (hK₀ (K₀.toAddSubgroup.nsmul_mem ha n)).2

  set S : AddSubgroup A := K₀.toAddSubgroup ⊔ lam.ker with hSdef
  have hSopen : IsOpen (S : Set A) :=
    AddSubgroup.isOpen_mono (le_sup_left : K₀.toAddSubgroup ≤ S) K₀.isOpen
  set C : Set A := (S : Set A)ᶜ
  have hCc : IsCompact C := hSopen.isClosed_compl.isCompact
  have hLc : IsClosed (lam '' C) := (hCc.image hlam).isClosed
  have h0 : (0 : V) ∉ lam '' C := by
    rintro ⟨c, hc, hc0⟩
    exact hc (le_sup_right (a := K₀.toAddSubgroup) (AddMonoidHom.mem_ker.2 hc0))
  refine ⟨(lam '' C)ᶜ, hLc.isOpen_compl.mem_nhds h0, fun a ha => ?_⟩
  have haS : a ∈ S := by
    by_contra h
    exact ha ⟨a, h, rfl⟩
  obtain ⟨k, hk, n, hn, rfl⟩ := AddSubgroup.mem_sup.1 haS
  rw [AddMonoidHom.mem_ker] at hn
  rw [hmul, hK₀one k hk, hker n hn, hn, hε0, mul_one, mul_one]

end GlobalTheory.CocycleChar
