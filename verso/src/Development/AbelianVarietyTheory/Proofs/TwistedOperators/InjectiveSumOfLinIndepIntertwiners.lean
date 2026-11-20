import Mathlib

namespace GlobalTheory

open Representation

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro φ _ w _`. Conclude with `Subsingleton.elim _ _`. Consider the case `succ m ih`.

Introduce `φ hφ`. Set `Φ : (Fin (m+1) → N) →ₗ[ℂ] X` to `∑ j, (φ j).toLinearMap ∘ₗ LinearMap.proj j`. Establish `hΦ : ∀ w, Φ w = ∑ j, φ j (w j)` using `by intro w; simp [Φ, LinearMap.sum_apply]`. Set `K` to `LinearMap.ker Φ`. Establish `hK : ∀ w, w ∈ K ↔ ∑ j, φ j (w j) = 0` using `by intro w; simp [K, hΦ]`.

Establish `hφ' : LinearIndependent ℂ (fun j : Fin m => φ j.castSucc)` using `hφ.comp _ (Fin.castSucc_injective m)`. Establish `claimA : ∀ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → w (Fin.last m) = 0 → w = 0`. Introduce `w hw hl`. Rewrite `hw` using `[Fin.sum_univ_castSucc, hl, map_zero, add_zero]`. Use `ih _ hφ' (fun j => w j.castSucc) hw` as an intermediate fact.

Use function extensionality and compare the values at `i`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `using hl`. Conclude with `congrFun this j`. Establish `hstable : ∀ (g : G) (w : Fin (m+1) → N), ∑ j, φ j (w j) = 0 → ∑ j, φ j (π g (w j)) = 0`.

Introduce `g w hw`. Repeatedly rewrite using `[IntertwiningMap.isIntertwining]`. Rewrite using `[← map_sum, hw, map_zero]`. Set `P : Subrepresentation π` to `{ toSubmodule := K.map (LinearMap.proj (Fin.last m)) apply_mem_toSubmodule := by`. Introduce and unpack `g _ ⟨w, hw, rfl⟩`.

Use `⟨fun j => π g (w j), ?_, rfl⟩` and prove the remaining obligations. Rewrite `hw`, the goal using `[SetLike.mem_coe, hK]`. Conclude with `hstable g w hw }`. Establish `hmemP : ∀ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → w (Fin.last m) ∈ P` using `fun w hw => show w (Fin.last m) ∈ K.map (LinearMap.proj (Fin.last m)) from ⟨w, (hK w).2 hw, rfl⟩`. Break down `hirr.eq_bot_or_eq_top P with hP | hP` into its components or cases.

Introduce `w hw`. Apply `claimA w hw` to reduce the goal to its premises. Use `hmemP w hw` as an intermediate fact. Rewrite `this` using `[hP]`. Conclude with `(Submodule.mem_bot ℂ).mp this`.

It suffices to derive a contradiction. Establish `hsurj : ∀ n : N, ∃ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 ∧ w (Fin.last m) = n`. Introduce `n`. Establish `: n ∈ P` using `by rw [hP]; exact Submodule.mem_top`. Take `⟨w, hw, rfl⟩` from `(show n ∈ K.map (LinearMap.proj (Fin.last m)) from this)`.

Conclude with `⟨w, (hK w).1 hw, rfl⟩`. Establish `huniq : ∀ w w' : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → ∑ j, φ j (w' j) = 0 → w (Fin.last m) = w' (Fin.last m) → w = w'`. Introduce `w w' hw hw' hl`. Use `claimA (w - w') (by simp [map_sub, Finset.sum_sub_distrib, hw, hw']) (by simp [hl])` as an intermediate fact. Conclude with `sub_eq_zero.mp this`.

Set `p : K →ₗ[ℂ] N` to `LinearMap.proj (Fin.last m) ∘ₗ K.subtype`. Establish `hp : Function.Bijective p`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Conclude with `Subtype.ext (huniq a.1 b.1 ((hK _).1 a.2) ((hK _).1 b.2) hab)`.

Introduce `n`. Take `⟨w, hw, hl⟩` from `hsurj n`. Conclude with `⟨⟨w, (hK w).2 hw⟩, hl⟩`. Set `e` to `LinearEquiv.ofBijective p hp`. Set `s : N →ₗ[ℂ] (Fin (m+1) → N)` to `K.subtype ∘ₗ e.symm.toLinearMap`.

Establish `hsK : ∀ n, ∑ j, φ j (s n j) = 0` using `fun n => (hK _).1 (e.symm n).2`. Establish `hsl : ∀ n, s n (Fin.last m) = n` using `fun n => e.apply_symm_apply n`. Establish `hsg : ∀ (g : G) (n : N), s (π g n) = fun j => π g (s n j)`. Introduce `g n`. Apply `huniq _ _ (hsK _) (hstable g _ (hsK n))` to reduce the goal to its premises.

Simplify using `only [hsl]`. Establish `hc : ∀ j : Fin m, ∃ c : ℂ, ∀ n, s n j.castSucc = c • n`. Introduce `j`. Set `f : π.IntertwiningMap π` to `{ toLinearMap := LinearMap.proj j.castSucc ∘ₗ s isIntertwining' := by`. Introduce `g`.

Use extensionality with `n`. Simplify using `[hsg] }`. Take `⟨c, hc⟩` from `hschur f`. Use `⟨c, fun n => ?_⟩` and prove the remaining obligations. Use `congrArg (fun L => L n) hc` as an intermediate fact.

Simplify `this` using `[f]`. Use `choose c hc using hc`. Establish `hrel : ∑ j : Fin m, c j • φ j.castSucc + φ (Fin.last m) = 0`. Use extensionality with `n`. Use `hsK n` as an intermediate fact.

Rewrite `this` using `[Fin.sum_univ_castSucc]`. Simplify using `only [hc, hsl, map_smul] at this`. Simplify `this` using `[IntertwiningMap.sum_apply]`. Use `(Fintype.linearIndependent_iff.mp hφ) (Fin.snoc c 1) (by` as an intermediate fact. Rewrite using `[Fin.sum_univ_castSucc]`.

Simplify using `using hrel)`. Establish `h1` using `this (Fin.last m)`. Simplify using `at h1`.
-/
theorem intertwiner_sum_eq_zero_imp {G : Type} [Group G] {N X : Type} [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X)
    (hirr : π.IsIrreducible)
    (hschur : ∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) :
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
      ∀ w : Fin m → N, ∑ j, φ j (w j) = 0 → w = 0 := by
  intro m
  induction m with
  | zero => intro φ _ w _; exact Subsingleton.elim _ _
  | succ m ih =>
    intro φ hφ
    let Φ : (Fin (m+1) → N) →ₗ[ℂ] X := ∑ j, (φ j).toLinearMap ∘ₗ LinearMap.proj j
    have hΦ : ∀ w, Φ w = ∑ j, φ j (w j) := by intro w; simp [Φ, LinearMap.sum_apply]
    let K := LinearMap.ker Φ
    have hK : ∀ w, w ∈ K ↔ ∑ j, φ j (w j) = 0 := by intro w; simp [K, hΦ]
    have hφ' : LinearIndependent ℂ (fun j : Fin m => φ j.castSucc) :=
      hφ.comp _ (Fin.castSucc_injective m)
    have claimA : ∀ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → w (Fin.last m) = 0 → w = 0 := by
      intro w hw hl
      rw [Fin.sum_univ_castSucc, hl, map_zero, add_zero] at hw
      have := ih _ hφ' (fun j => w j.castSucc) hw
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hl
      · exact congrFun this j
    have hstable : ∀ (g : G) (w : Fin (m+1) → N), ∑ j, φ j (w j) = 0 →
        ∑ j, φ j (π g (w j)) = 0 := by
      intro g w hw
      simp_rw [IntertwiningMap.isIntertwining]
      rw [← map_sum, hw, map_zero]
    let P : Subrepresentation π :=
      { toSubmodule := K.map (LinearMap.proj (Fin.last m))
        apply_mem_toSubmodule := by
          rintro g _ ⟨w, hw, rfl⟩
          refine ⟨fun j => π g (w j), ?_, rfl⟩
          rw [SetLike.mem_coe, hK] at hw ⊢
          exact hstable g w hw }
    have hmemP : ∀ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → w (Fin.last m) ∈ P := fun w hw =>
      show w (Fin.last m) ∈ K.map (LinearMap.proj (Fin.last m)) from ⟨w, (hK w).2 hw, rfl⟩
    rcases hirr.eq_bot_or_eq_top P with hP | hP
    · intro w hw
      apply claimA w hw
      have := hmemP w hw
      rw [hP] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exfalso
      have hsurj : ∀ n : N, ∃ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 ∧ w (Fin.last m) = n := by
        intro n
        have : n ∈ P := by rw [hP]; exact Submodule.mem_top
        obtain ⟨w, hw, rfl⟩ := (show n ∈ K.map (LinearMap.proj (Fin.last m)) from this)
        exact ⟨w, (hK w).1 hw, rfl⟩
      have huniq : ∀ w w' : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → ∑ j, φ j (w' j) = 0 →
          w (Fin.last m) = w' (Fin.last m) → w = w' := by
        intro w w' hw hw' hl
        have := claimA (w - w') (by simp [map_sub, Finset.sum_sub_distrib, hw, hw'])
          (by simp [hl])
        exact sub_eq_zero.mp this
      let p : K →ₗ[ℂ] N := LinearMap.proj (Fin.last m) ∘ₗ K.subtype
      have hp : Function.Bijective p := by
        constructor
        · intro a b hab
          exact Subtype.ext (huniq a.1 b.1 ((hK _).1 a.2) ((hK _).1 b.2) hab)
        · intro n
          obtain ⟨w, hw, hl⟩ := hsurj n
          exact ⟨⟨w, (hK w).2 hw⟩, hl⟩
      let e := LinearEquiv.ofBijective p hp
      let s : N →ₗ[ℂ] (Fin (m+1) → N) := K.subtype ∘ₗ e.symm.toLinearMap
      have hsK : ∀ n, ∑ j, φ j (s n j) = 0 := fun n => (hK _).1 (e.symm n).2
      have hsl : ∀ n, s n (Fin.last m) = n := fun n => e.apply_symm_apply n
      have hsg : ∀ (g : G) (n : N), s (π g n) = fun j => π g (s n j) := by
        intro g n
        apply huniq _ _ (hsK _) (hstable g _ (hsK n))
        simp only [hsl]
      have hc : ∀ j : Fin m, ∃ c : ℂ, ∀ n, s n j.castSucc = c • n := by
        intro j
        let f : π.IntertwiningMap π :=
          { toLinearMap := LinearMap.proj j.castSucc ∘ₗ s
            isIntertwining' := by
              intro g; ext n; simp [hsg] }
        obtain ⟨c, hc⟩ := hschur f
        refine ⟨c, fun n => ?_⟩
        have := congrArg (fun L => L n) hc
        simpa [f] using this
      choose c hc using hc
      have hrel : ∑ j : Fin m, c j • φ j.castSucc + φ (Fin.last m) = 0 := by
        ext n
        have := hsK n
        rw [Fin.sum_univ_castSucc] at this
        simp only [hc, hsl, map_smul] at this
        simpa [IntertwiningMap.sum_apply] using this
      have := (Fintype.linearIndependent_iff.mp hφ) (Fin.snoc c 1) (by
        rw [Fin.sum_univ_castSucc]; simpa using hrel)
      have h1 := this (Fin.last m)
      simp at h1

/- English proof (translation)
Introduce `G _ N X _ _ _ _ π ρ hirr hschur m φ hφ a b hab`. Use `intertwiner_sum_eq_zero_imp π ρ hirr hschur m φ hφ (a - b) (by simpa [map_sub, Finset.sum_sub_distrib, sub_eq_zero] using hab)` as an intermediate fact. Conclude with `sub_eq_zero.mp this`.
-/
theorem intertwiners_indep_injective : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible →
    (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) →
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
    Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)) := by
  intro G _ N X _ _ _ _ π ρ hirr hschur m φ hφ a b hab
  have := intertwiner_sum_eq_zero_imp π ρ hirr hschur m φ hφ (a - b)
    (by simpa [map_sub, Finset.sum_sub_distrib, sub_eq_zero] using hab)
  exact sub_eq_zero.mp this

end GlobalTheory
