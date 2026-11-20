import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.CentralProd2

open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC
open scoped TensorProduct

noncomputable section

namespace PositivityTheory.RgUd.Exp.Fact

/- English proof (translation)
Introduce `r t V W _ _ _ _ A B hAs hBs hI`. Take `⟨hX, hIirr⟩` from `(GlobalTheory.CuspRep.isIrreducible_iff _).1 hI`. Set `ρ'` to `(extTensor A B).comp (GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm.toMonoidHom`. Establish `hρ' : IsSmooth ρ'` using `isSmooth_comp (isSmooth_extTensor hAs hBs) _ (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from (continuous_apply false).prodMk (continuous_apply true))`. Establish `key : ∀ R : Submodule ℂ (V ⊗[ℂ] W), (∀ l, ∀ y ∈ R, ρ' l y ∈ R) → R = ⊥ ∨ R = ⊤`.

Introduce `R hR`. Set `Y : Submodule ℂ (IndSp (two (stdSum (rfl : r + t = r + t))) ρ')` to `{ carrier := {f | ∀ g, f.1.1 g ∈ R} add_mem' := fun ha hb g => add_mem (ha g) (hb g) zero_mem' := fun g => zero_mem R smul_mem' := fun c f hf g => R.smul_mem c (hf g) }`. Establish `hYs : ∀ g, ∀ f ∈ Y, prod₂ A B g f ∈ Y` using `fun g f hf x => hf (x * g)`. Break down `hIirr Y hYs with hY | hY` into its components or cases. Use `left`.

Use `(Submodule.eq_bot_iff R).2 fun u hu => ?_` and prove the remaining obligations. Take `⟨f, h1, h2⟩` from `GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' u`. Establish `hf : f ∈ Y` using `fun g => by`. Break down `h2 g with h | ⟨l, c, h⟩` into its components or cases. Rewrite using `[h]`.

Conclude with `zero_mem R`. Rewrite using `[h]`. Conclude with `R.smul_mem c (hR l u hu)`. Rewrite `hf` using `[hY, Submodule.mem_bot]`. Rewrite using `[← h1, hf]`.

Both sides reduce to the same expression. Use `right`. Use `eq_top_iff.2 fun u _ => ?_` and prove the remaining obligations. Take `⟨f, h1, -⟩` from `GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' u`. Establish `hf : f ∈ Y` using `by rw [hY]; exact Submodule.mem_top`.

Rewrite using `[← h1]`. Conclude with `hf 1`. Establish `h0 : ¬ ∀ z : V ⊗[ℂ] W, z = 0`. Introduce `h`. Take `⟨f₁, f₂, hne⟩` from `hX`.

Conclude with `hne (Subtype.ext (Subtype.ext (funext fun x => (h _).trans (h _).symm)))`. Establish `hV : Nontrivial V`. Assume the negation of the conclusion as `hV`. Rewrite `hV` using `[not_nontrivial_iff_subsingleton]`. Conclude with `h0 fun z => z.induction_on rfl (fun x w => by rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]) (fun a b ha hb => by rw [ha, hb, add_zero])`.

Establish `hW : Nontrivial W`. Assume the negation of the conclusion as `hW`. Rewrite `hW` using `[not_nontrivial_iff_subsingleton]`. Conclude with `h0 fun z => z.induction_on rfl (fun x w => by rw [Subsingleton.elim w 0, TensorProduct.tmul_zero]) (fun a b ha hb => by rw [ha, hb, add_zero])`. Use `⟨(GlobalTheory.CuspRep.isIrreducible_iff A).2 ⟨hV, fun S hS => ?_⟩, (GlobalTheory.CuspRep.isIrreducible_iff B).2 ⟨hW, fun S hS => ?_⟩⟩` and prove the remaining obligations.

Take `⟨w₀, hw₀⟩` from `exists_ne (0 : W)`. Choose the witnesses or unpack the hypotheses as in `⟨ψ, hψ⟩ : ∃ ψ : Module.Dual ℂ W, ψ w₀ ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hw₀ ((Module.forall_dual_apply_eq_zero_iff ℂ w₀).1 h)`.

Set `L : V ⊗[ℂ] W →ₗ[ℂ] V` to `(TensorProduct.rid ℂ V).toLinearMap ∘ₗ LinearMap.lTensor V ψ`. Establish `hL : ∀ x w, L (x ⊗ₜ w) = ψ w • x` using `fun x w => by simp [L]`. Set `R : Submodule ℂ (V ⊗[ℂ] W)` to `LinearMap.range (LinearMap.rTensor W S.subtype)`. Establish `hR : ∀ l, ∀ y ∈ R, ρ' l y ∈ R`. Introduce and unpack `l _ ⟨z, rfl⟩`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x w`. Conclude with `⟨⟨A ((GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm l).1 x, hS _ _ x.2⟩ ⊗ₜ B ((GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm l).2 w, by simp [ρ']⟩`. Consider the case `add a b ha hb`.

Rewrite using `[map_add, map_add]`. Conclude with `add_mem ha hb`. Establish `hLR : ∀ y ∈ R, L y ∈ S`. Introduce and unpack `_ ⟨z, rfl⟩`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul x w => rw [LinearMap.rTensor_tmul, hL]`. Conclude with `S.smul_mem _ x.2`. Consider the case `add a b ha hb => rw [map_add, map_add]`. Conclude with `add_mem ha hb`.

Break down `key R hR with h | h` into its components or cases. Use `left`. Use `(Submodule.eq_bot_iff S).2 fun s hs => ?_` and prove the remaining obligations. Establish `hm : s ⊗ₜ[ℂ] w₀ ∈ R` using `⟨⟨s, hs⟩ ⊗ₜ w₀, rfl⟩`. Rewrite `hm` using `[h, Submodule.mem_bot]`.

Establish `: L (s ⊗ₜ w₀) = 0` using `by rw [hm, map_zero]`. Rewrite `this` using `[hL]`. Conclude with `(smul_eq_zero.1 this).resolve_left hψ`. Use `right`. Use `eq_top_iff.2 fun v _ => ?_` and prove the remaining obligations.

Establish `hm : v ⊗ₜ[ℂ] w₀ ∈ R` using `by rw [h]; exact Submodule.mem_top`. Establish `h2` using `hLR _ hm`. Rewrite `h2` using `[hL]`. Conclude with `(S.smul_mem_iff hψ).1 h2`. Take `⟨x₀, hx₀⟩` from `exists_ne (0 : V)`.

Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ V, φ x₀ ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ x₀).1 h)`. Set `L : V ⊗[ℂ] W →ₗ[ℂ] W` to `(TensorProduct.lid ℂ W).toLinearMap ∘ₗ LinearMap.rTensor W φ`.

Establish `hL : ∀ x w, L (x ⊗ₜ w) = φ x • w` using `fun x w => by simp [L]`. Set `R : Submodule ℂ (V ⊗[ℂ] W)` to `LinearMap.range (LinearMap.lTensor V S.subtype)`. Establish `hR : ∀ l, ∀ y ∈ R, ρ' l y ∈ R`. Introduce and unpack `l _ ⟨z, rfl⟩`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul x w`. Conclude with `⟨A ((GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm l).1 x ⊗ₜ ⟨B ((GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm l).2 w, hS _ _ w.2⟩, by simp [ρ']⟩`. Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add]`.

Conclude with `add_mem ha hb`. Establish `hLR : ∀ y ∈ R, L y ∈ S`. Introduce and unpack `_ ⟨z, rfl⟩`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x w => rw [LinearMap.lTensor_tmul, hL]`. Conclude with `S.smul_mem _ w.2`. Consider the case `add a b ha hb => rw [map_add, map_add]`. Conclude with `add_mem ha hb`. Break down `key R hR with h | h` into its components or cases.

Use `left`. Use `(Submodule.eq_bot_iff S).2 fun s hs => ?_` and prove the remaining obligations. Establish `hm : x₀ ⊗ₜ[ℂ] s ∈ R` using `⟨x₀ ⊗ₜ ⟨s, hs⟩, rfl⟩`. Rewrite `hm` using `[h, Submodule.mem_bot]`. Establish `: L (x₀ ⊗ₜ s) = 0` using `by rw [hm, map_zero]`.

Rewrite `this` using `[hL]`. Conclude with `(smul_eq_zero.1 this).resolve_left hφ`. Use `right`. Use `eq_top_iff.2 fun v _ => ?_` and prove the remaining obligations. Establish `hm : x₀ ⊗ₜ[ℂ] v ∈ R` using `by rw [h]; exact Submodule.mem_top`.

Establish `h2` using `hLR _ hm`. Rewrite `h2` using `[hL]`. Conclude with `(S.smul_mem_iff hφ).1 h2`.
-/
theorem factorIrr (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.Exp.FactorIrr k := by
  intro r t V W _ _ _ _ A B hAs hBs hI
  classical
  obtain ⟨hX, hIirr⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hI
  let ρ' := (extTensor A B).comp (GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
  have hρ' : IsSmooth ρ' := isSmooth_comp (isSmooth_extTensor hAs hBs) _
    (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from
      (continuous_apply false).prodMk (continuous_apply true))
  have key : ∀ R : Submodule ℂ (V ⊗[ℂ] W), (∀ l, ∀ y ∈ R, ρ' l y ∈ R) → R = ⊥ ∨ R = ⊤ := by
    intro R hR
    let Y : Submodule ℂ (IndSp (two (stdSum (rfl : r + t = r + t))) ρ') :=
      { carrier := {f | ∀ g, f.1.1 g ∈ R}
        add_mem' := fun ha hb g => add_mem (ha g) (hb g)
        zero_mem' := fun g => zero_mem R
        smul_mem' := fun c f hf g => R.smul_mem c (hf g) }
    have hYs : ∀ g, ∀ f ∈ Y, prod₂ A B g f ∈ Y := fun g f hf x => hf (x * g)
    rcases hIirr Y hYs with hY | hY
    · left
      refine (Submodule.eq_bot_iff R).2 fun u hu => ?_
      obtain ⟨f, h1, h2⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' u
      have hf : f ∈ Y := fun g => by
        rcases h2 g with h | ⟨l, c, h⟩
        · rw [h]; exact zero_mem R
        · rw [h]; exact R.smul_mem c (hR l u hu)
      rw [hY, Submodule.mem_bot] at hf
      rw [← h1, hf]; rfl
    · right
      refine eq_top_iff.2 fun u _ => ?_
      obtain ⟨f, h1, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' u
      have hf : f ∈ Y := by rw [hY]; exact Submodule.mem_top
      rw [← h1]; exact hf 1
  have h0 : ¬ ∀ z : V ⊗[ℂ] W, z = 0 := by
    intro h
    obtain ⟨f₁, f₂, hne⟩ := hX
    exact hne (Subtype.ext (Subtype.ext (funext fun x => (h _).trans (h _).symm)))
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact h0 fun z => z.induction_on rfl
      (fun x w => by rw [Subsingleton.elim x 0, TensorProduct.zero_tmul])
      (fun a b ha hb => by rw [ha, hb, add_zero])
  have hW : Nontrivial W := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    exact h0 fun z => z.induction_on rfl
      (fun x w => by rw [Subsingleton.elim w 0, TensorProduct.tmul_zero])
      (fun a b ha hb => by rw [ha, hb, add_zero])
  refine ⟨(GlobalTheory.CuspRep.isIrreducible_iff A).2 ⟨hV, fun S hS => ?_⟩,
    (GlobalTheory.CuspRep.isIrreducible_iff B).2 ⟨hW, fun S hS => ?_⟩⟩
  · obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual ℂ W, ψ w₀ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw₀ ((Module.forall_dual_apply_eq_zero_iff ℂ w₀).1 h)
    let L : V ⊗[ℂ] W →ₗ[ℂ] V := (TensorProduct.rid ℂ V).toLinearMap ∘ₗ LinearMap.lTensor V ψ
    have hL : ∀ x w, L (x ⊗ₜ w) = ψ w • x := fun x w => by simp [L]
    let R : Submodule ℂ (V ⊗[ℂ] W) := LinearMap.range (LinearMap.rTensor W S.subtype)
    have hR : ∀ l, ∀ y ∈ R, ρ' l y ∈ R := by
      rintro l _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x w =>
        exact ⟨⟨A ((GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm l).1 x, hS _ _ x.2⟩ ⊗ₜ
          B ((GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm l).2 w, by simp [ρ']⟩
      | add a b ha hb =>
        rw [map_add, map_add]; exact add_mem ha hb
    have hLR : ∀ y ∈ R, L y ∈ S := by
      rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x w => rw [LinearMap.rTensor_tmul, hL]; exact S.smul_mem _ x.2
      | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
    rcases key R hR with h | h
    · left
      refine (Submodule.eq_bot_iff S).2 fun s hs => ?_
      have hm : s ⊗ₜ[ℂ] w₀ ∈ R := ⟨⟨s, hs⟩ ⊗ₜ w₀, rfl⟩
      rw [h, Submodule.mem_bot] at hm
      have : L (s ⊗ₜ w₀) = 0 := by rw [hm, map_zero]
      rw [hL] at this
      exact (smul_eq_zero.1 this).resolve_left hψ
    · right
      refine eq_top_iff.2 fun v _ => ?_
      have hm : v ⊗ₜ[ℂ] w₀ ∈ R := by rw [h]; exact Submodule.mem_top
      have h2 := hLR _ hm
      rw [hL] at h2
      exact (S.smul_mem_iff hψ).1 h2
  · obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ V, φ x₀ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ x₀).1 h)
    let L : V ⊗[ℂ] W →ₗ[ℂ] W := (TensorProduct.lid ℂ W).toLinearMap ∘ₗ LinearMap.rTensor W φ
    have hL : ∀ x w, L (x ⊗ₜ w) = φ x • w := fun x w => by simp [L]
    let R : Submodule ℂ (V ⊗[ℂ] W) := LinearMap.range (LinearMap.lTensor V S.subtype)
    have hR : ∀ l, ∀ y ∈ R, ρ' l y ∈ R := by
      rintro l _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x w =>
        exact ⟨A ((GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm l).1 x ⊗ₜ
          ⟨B ((GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm l).2 w, hS _ _ w.2⟩, by simp [ρ']⟩
      | add a b ha hb =>
        rw [map_add, map_add]; exact add_mem ha hb
    have hLR : ∀ y ∈ R, L y ∈ S := by
      rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x w => rw [LinearMap.lTensor_tmul, hL]; exact S.smul_mem _ w.2
      | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
    rcases key R hR with h | h
    · left
      refine (Submodule.eq_bot_iff S).2 fun s hs => ?_
      have hm : x₀ ⊗ₜ[ℂ] s ∈ R := ⟨x₀ ⊗ₜ ⟨s, hs⟩, rfl⟩
      rw [h, Submodule.mem_bot] at hm
      have : L (x₀ ⊗ₜ s) = 0 := by rw [hm, map_zero]
      rw [hL] at this
      exact (smul_eq_zero.1 this).resolve_left hφ
    · right
      refine eq_top_iff.2 fun v _ => ?_
      have hm : x₀ ⊗ₜ[ℂ] v ∈ R := by rw [h]; exact Submodule.mem_top
      have h2 := hLR _ hm
      rw [hL] at h2
      exact (S.smul_mem_iff hφ).1 h2

end PositivityTheory.RgUd.Exp.Fact
