import Mathlib

open Submodule

namespace GlobalTheory.SubmodulePowSimple

variable {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type}

def equivValues (a : ι → Module.End ℂ P) (m : ℕ) (N : Submodule ℂ (Fin m → P)) :
    Set (Fin m → P) :=
  {v | ∃ S : P →ₗ[ℂ] (Fin m → P), (∀ i p, S (a i p) = fun j => a i (S p j)) ∧
    (∀ p, S p ∈ N) ∧ ∃ q, v = S q}

def snocZero (m : ℕ) : (Fin m → P) →ₗ[ℂ] (Fin (m+1) → P) where
  toFun z := Fin.snoc (α := fun _ => P) z 0
  map_add' x y := by
    funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  map_smul' c x := by
    funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

/- English proof (translation)
Apply the tactic sequence `funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [snocZero]`.
-/
lemma snocZero_diag {m : ℕ} (b : Module.End ℂ P) (z : Fin m → P) :
    snocZero m (fun j => b (z j)) = fun j => b (snocZero m z j) := by
  funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [snocZero]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = Fin.last m`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`.
-/
lemma single_diag {m : ℕ} (b : Module.End ℂ P) (p : P) :
    (Pi.single (Fin.last m) (b p) : Fin (m+1) → P) = fun j => b ((Pi.single (Fin.last m) p : Fin (m+1) → P) j) := by
  funext j
  by_cases h : j = Fin.last m
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `N _ y _`. Rewrite using `[Subsingleton.elim y 0]`.

Conclude with `zero_mem _`. Consider the case `succ m ih`. Introduce `N hN y hy`. Set `B : Submodule ℂ P` to `N.comap (LinearMap.single ℂ (fun _ : Fin (m+1) => P) (Fin.last m))`. Establish `hBmem : ∀ p, p ∈ B ↔ (Pi.single (Fin.last m) p : Fin (m+1) → P) ∈ N` using `fun p => by`.

Simplify using `[B]`. Establish `hBst : ∀ i, ∀ p ∈ B, a i p ∈ B`. Introduce `i p hp`. Rewrite `hp`, the goal using `[hBmem]`. Rewrite using `[single_diag]`.

Conclude with `hN i _ hp`. Distinguish the cases in `hB : B = ⊥`. Set `I : (Fin (m+1) → P) →ₗ[ℂ] (Fin m → P)` to `LinearMap.funLeft ℂ P Fin.castSucc`. Establish `hinj : ∀ x₁ ∈ N, ∀ x₂ ∈ N, I x₁ = I x₂ → x₁ = x₂`. Introduce `x₁ h₁ x₂ h₂ he`.

Establish `hd : x₁ - x₂ ∈ N` using `N.sub_mem h₁ h₂`. Establish `hs' : x₁ - x₂ = Pi.single (Fin.last m) ((x₁ - x₂) (Fin.last m))`. Use function extensionality and compare the values at `j`. Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using the standard rewrite rules.

Establish `h` using `congrFun he j`. Express the relevant statement in the definitionally equal form `x₁ (Fin.castSucc j) = x₂ (Fin.castSucc j) at h`. Rewrite using `[Pi.single_eq_of_ne (Fin.castSucc_lt_last j).ne]`. Simplify using `[h]`. Establish `hB' : (x₁ - x₂) (Fin.last m) ∈ B`.

Rewrite using `[hBmem, ← hs']`. Conclude with `hd`. Rewrite `hB'` using `[hB, Submodule.mem_bot]`. Rewrite `hs'` using `[hB', Pi.single_zero]`. Conclude with `sub_eq_zero.mp hs'`.

Set `N0` to `N.map I`. Establish `hN0 : ∀ i, ∀ w ∈ N0, (fun j => a i (w j)) ∈ N0`. Introduce `i w hw`. Take `⟨x, hx, rfl⟩` from `hw`. Conclude with `⟨_, hN i x hx, rfl⟩`.

Establish `lift : ∀ S : P →ₗ[ℂ] (Fin m → P), (∀ p, S p ∈ N0) → ∃ S' : P →ₗ[ℂ] (Fin (m+1) → P), (∀ p, S' p ∈ N) ∧ ∀ p, I (S' p) = S p`. Introduce `S hS`. Set `J : N →ₗ[ℂ] (Fin m → P)` to `I ∘ₗ N.subtype`. Establish `hJ : Function.Injective J`. Introduce `u v huv`.

Conclude with `Subtype.ext (hinj u u.2 v v.2 huv)`. Establish `hS' : ∀ p, S p ∈ LinearMap.range J`. Introduce `p`. Take `⟨x, hx, hxe⟩` from `hS p`. Conclude with `⟨⟨x, hx⟩, hxe⟩`.

Establish `key : ∀ v, J ((LinearEquiv.ofInjective J hJ).symm v) = v` using `fun v => by`. Establish `h` using `congrArg Subtype.val ((LinearEquiv.ofInjective J hJ).apply_symm_apply v)`. Rewrite `h` using `[LinearEquiv.ofInjective_apply]`. Conclude with `h`. Use `⟨N.subtype ∘ₗ (LinearEquiv.ofInjective J hJ).symm.toLinearMap ∘ₗ S.codRestrict _ hS', fun p => Subtype.property _, fun p => ?_⟩` and prove the remaining obligations.

Conclude with `key ⟨S p, hS' p⟩`. Establish `h1` using `ih N0 hN0 (I y) ⟨y, hy, rfl⟩`. Take `⟨n, f, g, hfg⟩` from `(Submodule.mem_span_set').mp h1`. Establish `hg : ∀ k, ∃ S : P →ₗ[ℂ] (Fin m → P), (∀ i p, S (a i p) = fun j => a i (S p j)) ∧ (∀ p, S p ∈ N0) ∧ ∃ q, (g k : Fin m → P) = S q` using `fun k => (g k).2`. Use `choose S hSa hSN q hq using hg`.

Use `choose S' hS'N hS'I using fun k => lift (S k) (hSN k)`. Establish `hS'a : ∀ k i p, S' k (a i p) = fun j => a i (S' k p j)`. Introduce `k i p`. Apply `hinj _ (hS'N k _) _ (hN i _ (hS'N k p))` to reduce the goal to its premises. Rewrite using `[hS'I, hSa, ← hS'I k p]`.

Both sides reduce to the same expression. Establish `hy_eq : y = ∑ k, f k • S' k (q k)`. Apply `hinj _ hy _ (sum_mem fun k _ => N.smul_mem _ (hS'N k _))` to reduce the goal to its premises. Rewrite using `[← hfg, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, hS'I, hq]`. Rewrite using `[hy_eq]`. Conclude with `sum_mem fun k _ => smul_mem _ _ (subset_span ⟨S' k, hS'a k, hS'N k, q k, rfl⟩)`. Establish `hBt` using `hs B hBst hB`. Establish `hmem : ∀ p, (Pi.single (Fin.last m) p : Fin (m+1) → P) ∈ N` using `fun p => by`.

Rewrite using `[← hBmem, hBt]`. Conclude with `Submodule.mem_top`. Take `⟨y', hy'⟩ : ∃ y', y' = y - Pi.single (Fin.last m) (y (Fin.last m))` from `⟨_, rfl⟩`. Establish `hy'N : y' ∈ N` using `hy' ▸ N.sub_mem hy (hmem _)`. Establish `hy'last : y' (Fin.last m) = 0` using `by simp [hy']`.

Set `N'` to `N.comap (snocZero m)`. Establish `hN' : ∀ i, ∀ z ∈ N', (fun j => a i (z j)) ∈ N'`. Introduce `i z hz`. Use `show snocZero m _ ∈ N`. Rewrite using `[snocZero_diag]`.

Conclude with `hN i _ hz`. Set `z : Fin m → P` to `fun j => y' (Fin.castSucc j)`. Establish `hz : snocZero m z = y'`. Use function extensionality and compare the values at `j`. Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations.

Simplify using `[snocZero, hy'last]`. Simplify using `[snocZero, z]`. Establish `hzN' : z ∈ N'` using `show snocZero m z ∈ N from hz ▸ hy'N`. Establish `h1` using `ih N' hN' z hzN'`. Establish `h2 : y' ∈ span ℂ (equivValues a (m+1) N)`.

Rewrite using `[← hz]`. Establish `h` using `Submodule.mem_map_of_mem (f := snocZero m) h1`. Rewrite `h` using `[Submodule.map_span]`. Use `Submodule.span_mono ?_ h` and prove the remaining obligations. Introduce and unpack `_ ⟨v, ⟨S, hSa, hSN, q, rfl⟩, rfl⟩`.

Use `⟨snocZero m ∘ₗ S, ?_, fun p => hSN p, q, rfl⟩` and prove the remaining obligations. Introduce `i p`. Simplify using `only [LinearMap.comp_apply, hSa, snocZero_diag]`. Establish `h3 : (Pi.single (Fin.last m) (y (Fin.last m)) : Fin (m+1) → P) ∈ span ℂ (equivValues a (m+1) N)`. Use `Submodule.subset_span ⟨LinearMap.single ℂ (fun _ : Fin (m+1) => P) (Fin.last m), ?_, ?_, y (Fin.last m), rfl⟩` and prove the remaining obligations.

Introduce `i p`. Simplify using `only [LinearMap.single_apply]`. Conclude with `single_diag _ _`. Introduce `p`. Simplify using `using hmem p`.

Establish `: y = y' + Pi.single (Fin.last m) (y (Fin.last m))` using `by simp [hy']`. Rewrite using `[this]`. Conclude with `add_mem h2 h3`.
-/
theorem mem_span_equivValues (a : ι → Module.End ℂ P)
    (hs : ∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) :
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, y ∈ span ℂ (equivValues a m N) := by
  intro m
  induction m with
  | zero =>
    intro N _ y _
    rw [Subsingleton.elim y 0]; exact zero_mem _
  | succ m ih =>
    intro N hN y hy
    let B : Submodule ℂ P := N.comap (LinearMap.single ℂ (fun _ : Fin (m+1) => P) (Fin.last m))
    have hBmem : ∀ p, p ∈ B ↔ (Pi.single (Fin.last m) p : Fin (m+1) → P) ∈ N := fun p => by
      simp [B]
    have hBst : ∀ i, ∀ p ∈ B, a i p ∈ B := by
      intro i p hp
      rw [hBmem] at hp ⊢
      rw [single_diag]; exact hN i _ hp
    by_cases hB : B = ⊥
    · let I : (Fin (m+1) → P) →ₗ[ℂ] (Fin m → P) := LinearMap.funLeft ℂ P Fin.castSucc
      have hinj : ∀ x₁ ∈ N, ∀ x₂ ∈ N, I x₁ = I x₂ → x₁ = x₂ := by
        intro x₁ h₁ x₂ h₂ he
        have hd : x₁ - x₂ ∈ N := N.sub_mem h₁ h₂
        have hs' : x₁ - x₂ = Pi.single (Fin.last m) ((x₁ - x₂) (Fin.last m)) := by
          funext j; refine Fin.lastCases ?_ (fun j => ?_) j
          · simp
          · have h := congrFun he j
            change x₁ (Fin.castSucc j) = x₂ (Fin.castSucc j) at h
            rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last j).ne]
            simp [h]
        have hB' : (x₁ - x₂) (Fin.last m) ∈ B := by
          rw [hBmem, ← hs']; exact hd
        rw [hB, Submodule.mem_bot] at hB'
        rw [hB', Pi.single_zero] at hs'
        exact sub_eq_zero.mp hs'
      let N0 := N.map I
      have hN0 : ∀ i, ∀ w ∈ N0, (fun j => a i (w j)) ∈ N0 := by
        intro i w hw
        obtain ⟨x, hx, rfl⟩ := hw
        exact ⟨_, hN i x hx, rfl⟩
      have lift : ∀ S : P →ₗ[ℂ] (Fin m → P), (∀ p, S p ∈ N0) →
          ∃ S' : P →ₗ[ℂ] (Fin (m+1) → P), (∀ p, S' p ∈ N) ∧ ∀ p, I (S' p) = S p := by
        intro S hS
        let J : N →ₗ[ℂ] (Fin m → P) := I ∘ₗ N.subtype
        have hJ : Function.Injective J := by
          intro u v huv; exact Subtype.ext (hinj u u.2 v v.2 huv)
        have hS' : ∀ p, S p ∈ LinearMap.range J := by
          intro p; obtain ⟨x, hx, hxe⟩ := hS p; exact ⟨⟨x, hx⟩, hxe⟩
        have key : ∀ v, J ((LinearEquiv.ofInjective J hJ).symm v) = v := fun v => by
          have h := congrArg Subtype.val ((LinearEquiv.ofInjective J hJ).apply_symm_apply v)
          rw [LinearEquiv.ofInjective_apply] at h
          exact h
        refine ⟨N.subtype ∘ₗ (LinearEquiv.ofInjective J hJ).symm.toLinearMap ∘ₗ
          S.codRestrict _ hS', fun p => Subtype.property _, fun p => ?_⟩
        exact key ⟨S p, hS' p⟩
      have h1 := ih N0 hN0 (I y) ⟨y, hy, rfl⟩
      obtain ⟨n, f, g, hfg⟩ := (Submodule.mem_span_set').mp h1
      have hg : ∀ k, ∃ S : P →ₗ[ℂ] (Fin m → P), (∀ i p, S (a i p) = fun j => a i (S p j)) ∧
          (∀ p, S p ∈ N0) ∧ ∃ q, (g k : Fin m → P) = S q := fun k => (g k).2
      choose S hSa hSN q hq using hg
      choose S' hS'N hS'I using fun k => lift (S k) (hSN k)
      have hS'a : ∀ k i p, S' k (a i p) = fun j => a i (S' k p j) := by
        intro k i p
        apply hinj _ (hS'N k _) _ (hN i _ (hS'N k p))
        rw [hS'I, hSa, ← hS'I k p]; rfl
      have hy_eq : y = ∑ k, f k • S' k (q k) := by
        apply hinj _ hy _ (sum_mem fun k _ => N.smul_mem _ (hS'N k _))
        rw [← hfg, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, hS'I, hq]
      rw [hy_eq]
      exact sum_mem fun k _ => smul_mem _ _ (subset_span ⟨S' k, hS'a k, hS'N k, q k, rfl⟩)
    · have hBt := hs B hBst hB
      have hmem : ∀ p, (Pi.single (Fin.last m) p : Fin (m+1) → P) ∈ N := fun p => by
        rw [← hBmem, hBt]; exact Submodule.mem_top
      obtain ⟨y', hy'⟩ : ∃ y', y' = y - Pi.single (Fin.last m) (y (Fin.last m)) := ⟨_, rfl⟩
      have hy'N : y' ∈ N := hy' ▸ N.sub_mem hy (hmem _)
      have hy'last : y' (Fin.last m) = 0 := by simp [hy']
      let N' := N.comap (snocZero m)
      have hN' : ∀ i, ∀ z ∈ N', (fun j => a i (z j)) ∈ N' := by
        intro i z hz
        show snocZero m _ ∈ N
        rw [snocZero_diag]; exact hN i _ hz
      let z : Fin m → P := fun j => y' (Fin.castSucc j)
      have hz : snocZero m z = y' := by
        funext j; refine Fin.lastCases ?_ (fun j => ?_) j
        · simp [snocZero, hy'last]
        · simp [snocZero, z]
      have hzN' : z ∈ N' := show snocZero m z ∈ N from hz ▸ hy'N
      have h1 := ih N' hN' z hzN'
      have h2 : y' ∈ span ℂ (equivValues a (m+1) N) := by
        rw [← hz]
        have h := Submodule.mem_map_of_mem (f := snocZero m) h1
        rw [Submodule.map_span] at h
        refine Submodule.span_mono ?_ h
        rintro _ ⟨v, ⟨S, hSa, hSN, q, rfl⟩, rfl⟩
        refine ⟨snocZero m ∘ₗ S, ?_, fun p => hSN p, q, rfl⟩
        intro i p; simp only [LinearMap.comp_apply, hSa, snocZero_diag]
      have h3 : (Pi.single (Fin.last m) (y (Fin.last m)) : Fin (m+1) → P) ∈
          span ℂ (equivValues a (m+1) N) := by
        refine Submodule.subset_span
          ⟨LinearMap.single ℂ (fun _ : Fin (m+1) => P) (Fin.last m), ?_, ?_, y (Fin.last m), rfl⟩
        · intro i p; simp only [LinearMap.single_apply]; exact single_diag _ _
        · intro p; simpa using hmem p
      have : y = y' + Pi.single (Fin.last m) (y (Fin.last m)) := by simp [hy']
      rw [this]; exact add_mem h2 h3

end GlobalTheory.SubmodulePowSimple

namespace GlobalTheory

/- English proof (translation)
Introduce `P _ _ ι a hs m N hN y hy`. Take `⟨n, f, g, hfg⟩` from `(Submodule.mem_span_set').mp (SubmodulePowSimple.mem_span_equivValues a hs m N hN y hy)`. Establish `hg : ∀ k, ∃ S : P →ₗ[ℂ] (Fin m → P), (∀ i p, S (a i p) = fun j => a i (S p j)) ∧ (∀ p, S p ∈ N) ∧ ∃ q, (g k : Fin m → P) = S q` using `fun k => (g k).2`. Use `choose S hSa hSN q hq using hg`. Use `⟨n, S, fun k => f k • q k, hSa, hSN, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hfg]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hq, map_smul]`.
-/
theorem submodule_pow_simple_eq_sum_equiv_values :
    ∀ {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type} (a : ι → Module.End ℂ P),
    (∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) →
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, ∃ (n : ℕ) (Sm : Fin n → (P →ₗ[ℂ] (Fin m → P))) (q : Fin n → P),
      (∀ l i p, Sm l (a i p) = fun j => a i (Sm l p j)) ∧ (∀ l p, Sm l p ∈ N) ∧
        y = ∑ l, Sm l (q l) := by
  intro P _ _ ι a hs m N hN y hy
  obtain ⟨n, f, g, hfg⟩ :=
    (Submodule.mem_span_set').mp (SubmodulePowSimple.mem_span_equivValues a hs m N hN y hy)
  have hg : ∀ k, ∃ S : P →ₗ[ℂ] (Fin m → P), (∀ i p, S (a i p) = fun j => a i (S p j)) ∧
      (∀ p, S p ∈ N) ∧ ∃ q, (g k : Fin m → P) = S q := fun k => (g k).2
  choose S hSa hSN q hq using hg
  refine ⟨n, S, fun k => f k • q k, hSa, hSN, ?_⟩
  rw [← hfg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hq, map_smul]

end GlobalTheory
