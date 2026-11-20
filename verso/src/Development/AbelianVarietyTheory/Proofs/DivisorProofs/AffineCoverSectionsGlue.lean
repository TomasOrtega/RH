import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecEquivResM

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue

namespace GlobalTheory.AffGlue.Cech

variable {T : Scheme.{0}}

/- English proof (translation)
Rewrite using `[← hV.self_le_iSup_basicOpen_iff]`. Introduce `x hx`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hc hx)`. Take `⟨f, hf, hxf⟩` from `hV.exists_basicOpen_le (V := W i) ⟨x, hi⟩ hx`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, i, hf⟩, hxf⟩`.
-/
theorem span_small_eq_top {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens)
    (hc : V ≤ ⨆ i, W i) :
    Ideal.span {f : Γ(T, V) | ∃ i, T.basicOpen f ≤ W i} = ⊤ := by
  rw [← hV.self_le_iSup_basicOpen_iff]
  intro x hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc hx)
  obtain ⟨f, hf, hxf⟩ := hV.exists_basicOpen_le (V := W i) ⟨x, hi⟩ hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, i, hf⟩, hxf⟩

/- English proof (translation)
Use `Submodule.mem_of_span_eq_top_of_smul_pow_mem (⊥ : Submodule Γ(T, V) (D.M V hV)) _ (span_small_eq_top hV W hc) x (by` as an intermediate fact. Introduce and unpack `⟨f, i, hf⟩`. Take `⟨n, hn⟩` from `D.loc_inj hV f (hV.basicOpen f) x (hx i _ _ _ hf)`. Conclude with `⟨n, by simpa using hn⟩)`. Simplify using `using this`.
-/
theorem eq_zero_of_small (D : Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type}
    (W : ι → T.Opens) (hc : V ≤ ⨆ i, W i) (x : D.M V hV)
    (hx : ∀ (i : ι) (O : T.Opens) (hO : IsAffineOpen O) (h : O ≤ V), O ≤ W i →
      D.ρ hV hO h x = 0) : x = 0 := by
  have := Submodule.mem_of_span_eq_top_of_smul_pow_mem (⊥ : Submodule Γ(T, V) (D.M V hV)) _
    (span_small_eq_top hV W hc) x (by
      rintro ⟨f, i, hf⟩
      obtain ⟨n, hn⟩ := D.loc_inj hV f (hV.basicOpen f) x (hx i _ _ _ hf)
      exact ⟨n, by simpa using hn⟩)
  simpa using this

/- English proof (translation)
Set `I : Ideal Γ(T, V)` to `{ carrier := {a | ∃ x : D.M V hV, ∀ k ∈ s, D.ρ hV (hW k) (hWV k) x = resG T (hWV k) a • m k} add_mem' := by`. Introduce and unpack `a b ⟨x, hx⟩ ⟨y, hy⟩`. Conclude with `⟨x + y, fun k hk => by rw [map_add, map_add, add_smul, hx k hk, hy k hk]⟩`. Use the proof step `zero_mem' := ⟨0, fun k _ => by rw [map_zero, map_zero, zero_smul]⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `c a ⟨x, hx⟩`. Conclude with `⟨c • x, fun k hk => by`. Rewrite using `[D.ρ_smul, hx k hk, smul_eq_mul, map_mul, mul_smul]⟩ }`. Establish `h1 : (1 : Γ(T, V)) ∈ I`. Use `Submodule.mem_of_span_eq_top_of_smul_pow_mem I _ (span_small_eq_top hV W hc) 1 ?_` and prove the remaining obligations.

Introduce and unpack `⟨f, i, hf⟩`. Take `⟨N, x₀, hx₀⟩` from `D.loc_surj hV f (hV.basicOpen f) (D.ρ (hW i) (hV.basicOpen f) hf (m i))`. Establish `key : ∀ k, ∃ e : ℕ, resG T (hWV k) f ^ e • (D.ρ hV (hW k) (hWV k) x₀ - resG T (hWV k) f ^ N • m k) = 0`. Introduce `k`. Use `D.loc_inj (hW k) (resG T (hWV k) f) ((hW k).basicOpen _) _ ?_` and prove the remaining obligations.

Establish `hle : T.basicOpen (resG T (hWV k) f) ≤ T.basicOpen f`. Use `T.basicOpen_res f (homOfLE (hWV k)).op` as an intermediate fact. Conclude with `(le_of_eq this).trans inf_le_right`. Establish `h2` using `congrArg (D.ρ (hV.basicOpen f) ((hW k).basicOpen (resG T (hWV k) f)) hle) hx₀`. Rewrite `h2` using `[D.ρ_ρ, D.ρ_smul, D.ρ_ρ, map_pow, resG_resG' _ _ (hle.trans (T.basicOpen_le f))]`.

Rewrite using `[map_sub, D.ρ_ρ, D.ρ_smul, map_pow, resG_resG' _ _ (hle.trans (T.basicOpen_le f)), ← h2, hm i k _ _ _ (T.basicOpen_le _), sub_self]`. Use `choose e he using key`. Use `⟨s.sup e + N, f ^ s.sup e • x₀, fun k hk => ?_⟩` and prove the remaining obligations. Establish `hk' : e k ≤ s.sup e` using `Finset.le_sup hk`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le' hk'`.

Establish `h3 : resG T (hWV k) f ^ s.sup e • (D.ρ hV (hW k) (hWV k) x₀ - resG T (hWV k) f ^ N • m k) = 0`. Rewrite using `[hd, pow_add, mul_smul, he, smul_zero]`. Rewrite `h3` using `[smul_sub, sub_eq_zero]`. Rewrite using `[D.ρ_smul, map_pow, h3, smul_eq_mul, mul_one, map_pow, pow_add, mul_smul]`. Take `⟨x, hx⟩` from `h1`.

Conclude with `⟨x, fun k hk => by rw [hx k hk, map_one, one_smul]⟩`.
-/
theorem exists_glue_finset (D : Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type}
    (W : ι → T.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V) (hc : V ≤ ⨆ i, W i)
    (m : ∀ i, D.M (W i) (hW i))
    (hm : ∀ (i j : ι) (O : T.Opens) (hO : IsAffineOpen O) (hi : O ≤ W i) (hj : O ≤ W j),
      D.ρ (hW i) hO hi (m i) = D.ρ (hW j) hO hj (m j)) (s : Finset ι) :
    ∃ x : D.M V hV, ∀ k ∈ s, D.ρ hV (hW k) (hWV k) x = m k := by
  let I : Ideal Γ(T, V) :=
    { carrier := {a | ∃ x : D.M V hV, ∀ k ∈ s, D.ρ hV (hW k) (hWV k) x = resG T (hWV k) a • m k}
      add_mem' := by
        rintro a b ⟨x, hx⟩ ⟨y, hy⟩
        exact ⟨x + y, fun k hk => by rw [map_add, map_add, add_smul, hx k hk, hy k hk]⟩
      zero_mem' := ⟨0, fun k _ => by rw [map_zero, map_zero, zero_smul]⟩
      smul_mem' := by
        rintro c a ⟨x, hx⟩
        exact ⟨c • x, fun k hk => by
          rw [D.ρ_smul, hx k hk, smul_eq_mul, map_mul, mul_smul]⟩ }
  have h1 : (1 : Γ(T, V)) ∈ I := by
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem I _ (span_small_eq_top hV W hc) 1 ?_
    rintro ⟨f, i, hf⟩
    obtain ⟨N, x₀, hx₀⟩ := D.loc_surj hV f (hV.basicOpen f)
      (D.ρ (hW i) (hV.basicOpen f) hf (m i))
    have key : ∀ k, ∃ e : ℕ, resG T (hWV k) f ^ e •
        (D.ρ hV (hW k) (hWV k) x₀ - resG T (hWV k) f ^ N • m k) = 0 := by
      intro k
      refine D.loc_inj (hW k) (resG T (hWV k) f) ((hW k).basicOpen _) _ ?_
      have hle : T.basicOpen (resG T (hWV k) f) ≤ T.basicOpen f := by
        have := T.basicOpen_res f (homOfLE (hWV k)).op
        exact (le_of_eq this).trans inf_le_right
      have h2 := congrArg (D.ρ (hV.basicOpen f) ((hW k).basicOpen (resG T (hWV k) f)) hle) hx₀
      rw [D.ρ_ρ, D.ρ_smul, D.ρ_ρ, map_pow, resG_resG' _ _ (hle.trans (T.basicOpen_le f))] at h2
      rw [map_sub, D.ρ_ρ, D.ρ_smul, map_pow, resG_resG' _ _ (hle.trans (T.basicOpen_le f)),
        ← h2, hm i k _ _ _ (T.basicOpen_le _), sub_self]
    choose e he using key
    refine ⟨s.sup e + N, f ^ s.sup e • x₀, fun k hk => ?_⟩
    have hk' : e k ≤ s.sup e := Finset.le_sup hk
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hk'
    have h3 : resG T (hWV k) f ^ s.sup e •
        (D.ρ hV (hW k) (hWV k) x₀ - resG T (hWV k) f ^ N • m k) = 0 := by
      rw [hd, pow_add, mul_smul, he, smul_zero]
    rw [smul_sub, sub_eq_zero] at h3
    rw [D.ρ_smul, map_pow, h3, smul_eq_mul, mul_one, map_pow, pow_add, mul_smul]
  obtain ⟨x, hx⟩ := h1
  exact ⟨x, fun k hk => by rw [hx k hk, map_one, one_smul]⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `hV.isCompact.elim_finite_subcover (fun i => (W i : Set T)) (fun i => (W i).isOpen) (fun x hx => by`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hc hx)`. Conclude with `Set.mem_iUnion.2 ⟨i, hi⟩)`. Take `⟨x, hx⟩` from `exists_glue_finset D hV W hW hWV hc m hm s`. Use `⟨x, fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_small D (hW i) (fun k : s => W k) (fun y hy => ?_) _ ?_` and prove the remaining obligations. Take `⟨k, hk, hyk⟩` from `Set.mem_iUnion₂.1 (hs (hWV i hy))`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, hk⟩, hyk⟩`. Introduce and unpack `⟨k, hk⟩ O hO h hOk`.

Rewrite using `[map_sub, D.ρ_ρ, hm i k O hO h hOk, ← hx k hk, D.ρ_ρ, sub_self]`.
-/
theorem exists_glue {T : Scheme.{0}} (D : GlobalTheory.AffGlue.Data T) {V : T.Opens} (hV : IsAffineOpen V)
    {ι : Type} (W : ι → T.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V)
    (hc : V ≤ ⨆ i, W i) (m : ∀ i, D.M (W i) (hW i))
    (hm : ∀ (i j : ι) (O : T.Opens) (hO : IsAffineOpen O) (hi : O ≤ W i) (hj : O ≤ W j),
      D.ρ (hW i) hO hi (m i) = D.ρ (hW j) hO hj (m j)) :
    ∃ x : D.M V hV, ∀ i, D.ρ hV (hW i) (hWV i) x = m i := by
  obtain ⟨s, hs⟩ := hV.isCompact.elim_finite_subcover (fun i => (W i : Set T))
    (fun i => (W i).isOpen) (fun x hx => by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc hx)
      exact Set.mem_iUnion.2 ⟨i, hi⟩)
  obtain ⟨x, hx⟩ := exists_glue_finset D hV W hW hWV hc m hm s
  refine ⟨x, fun i => ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_small D (hW i) (fun k : s => W k) (fun y hy => ?_) _ ?_
  · obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 (hs (hWV i hy))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, hk⟩, hyk⟩
  · rintro ⟨k, hk⟩ O hO h hOk
    rw [map_sub, D.ρ_ρ, hm i k O hO h hOk, ← hx k hk, D.ρ_ρ, sub_self]

end GlobalTheory.AffGlue.Cech
