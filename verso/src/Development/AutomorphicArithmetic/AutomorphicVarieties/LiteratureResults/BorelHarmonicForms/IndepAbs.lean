import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

/- English proof (translation)
Introduce `O W _ _ A s V h hs hn`. Establish `hsup : ∀ P Q : Submodule ℂ W, (∀ o, ∀ x ∈ P, A o x ∈ P) → (∀ o, ∀ x ∈ Q, A o x ∈ Q) → ∀ o, ∀ x ∈ P ⊔ Q, A o x ∈ P ⊔ Q`. Introduce `P Q hP hQ o x hx`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hx`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem_sup (hP o y hy) (hQ o z hz)`. Establish `hfs : ∀ t : Finset (Fin s), ∀ o, ∀ x ∈ t.sup V, A o x ∈ t.sup V`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`.

Introduce `o x hx`. Simplify using `only [Finset.sup_empty, Submodule.mem_bot] at hx ⊢`. Rewrite using `[hx, map_zero]`. Consider the case `insert j t hj ih`. Rewrite using `[Finset.sup_insert]`.

Conclude with `hsup _ _ (h j) ih`. Establish `key : ∀ t : Finset (Fin s), ∀ i, i ∉ t → Disjoint (V i) (t.sup V)`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => intro i _`.

Simplify using the standard rewrite rules. Consider the case `insert j t hj ih`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_insert, not_or]`. Take `⟨hij, hit⟩` from `hi`.

Establish `hSinv` using `hfs t`. Establish `hiS` using `ih i hit`. Establish `hjS` using `ih j hj`. Rewrite using `[Finset.sup_insert, disjoint_iff]`. Use `set S := t.sup V with hSdef`.

Distinguish the cases in `hVi : V i = ⊥`. Rewrite using `[hVi, bot_inf_eq]`. Establish `hM : ∀ o, ∀ x ∈ V i ⊓ (V j ⊔ S), A o x ∈ V i ⊓ (V j ⊔ S)` using `fun o x hx => ⟨h i o x hx.1, hsup _ _ (h j) hSinv o x hx.2⟩`. Break down `hs i _ inf_le_left hM with hbot | htop` into its components or cases. Conclude with `hbot`.

It suffices to derive a contradiction. Establish `hle : V i ≤ V j ⊔ S` using `inf_eq_left.mp htop`. Establish `huniq : ∀ y y' : V j, ((y : W) - y') ∈ S → y = y'`. Introduce `y y' hyy`. Establish `h0 : ((y : W) - y') ∈ V j ⊓ S` using `⟨sub_mem y.2 y'.2, hyy⟩`.

Rewrite `h0` using `[disjoint_iff.mp hjS, Submodule.mem_bot, sub_eq_zero]`. Conclude with `Subtype.ext h0`. Set `fj : V j →ₗ[ℂ] W ⧸ S` to `S.mkQ ∘ₗ (V j).subtype`. Establish `hfj : Function.Injective fj`. Introduce `a b hab`.

Conclude with `huniq a b ((Submodule.Quotient.eq S).mp hab)`. Set `ej` to `LinearEquiv.ofInjective fj hfj`. Set `fi : V i →ₗ[ℂ] W ⧸ S` to `S.mkQ ∘ₗ (V i).subtype`. Establish `hrange : ∀ x : V i, fi x ∈ LinearMap.range fj`. Introduce `x`.

Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp (hle x.2)`. Use `⟨⟨y, hy⟩, ?_⟩` and prove the remaining obligations. Use `show S.mkQ y = S.mkQ x`. Rewrite using `[← hyz, map_add, Submodule.mkQ_apply S z, (Submodule.Quotient.mk_eq_zero S).mpr hz, add_zero]`. Set `T : V i →ₗ[ℂ] V j` to `ej.symm.toLinearMap ∘ₗ (fi.codRestrict (LinearMap.range fj) hrange)`.

Establish `hT : ∀ x : V i, ((T x : W) - x) ∈ S`. Introduce `x`. Establish `e0 : T x = ej.symm ⟨fi x, hrange x⟩` using `rfl`. Establish `e1` using `ej.apply_symm_apply ⟨fi x, hrange x⟩`. Rewrite `e1` using `[Subtype.ext_iff, LinearEquiv.ofInjective_apply, ← e0]`.

Conclude with `(Submodule.Quotient.eq S).mp e1`. Establish `hTeq : ∀ o (x : V i), T ((A o).restrict (h i o) x) = (A o).restrict (h j o) (T x)`. Introduce `o x`. Apply `huniq` to reduce the goal to its premises. Establish `e1` using `hT ((A o).restrict (h i o) x)`.

Establish `e2 : A o ((T x : W) - x) ∈ S` using `hSinv o _ (hT x)`. Establish `e3 : ((T ((A o).restrict (h i o) x) : W) - ((A o).restrict (h j o) (T x) : W)) = ((T ((A o).restrict (h i o) x) : W) - ((A o).restrict (h i o) x : W)) - A o ((T x : W) - x)`. Simplify using `only [LinearMap.restrict_coe_apply, map_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e3]`.

Conclude with `sub_mem e1 e2`. Establish `hTinj : Function.Injective T`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `x hx`. Rewrite `hx` using `[LinearMap.mem_ker]`.

Establish `e1` using `hT x`. Rewrite `e1` using `[hx, Submodule.coe_zero, zero_sub]`. Establish `hxS : (x : W) ∈ S` using `by simpa using S.neg_mem e1`. Establish `e2 : (x : W) ∈ V i ⊓ S` using `⟨x.2, hxS⟩`. Rewrite `e2` using `[disjoint_iff.mp hiS, Submodule.mem_bot]`.

Conclude with `(Submodule.mem_bot ℂ).mpr (Subtype.ext e2)`. Set `N` to `(LinearMap.range T).map (V j).subtype`. Establish `hNle : N ≤ V j` using `Submodule.map_subtype_le _ _`. Establish `hNinv : ∀ o, ∀ x ∈ N, A o x ∈ N`. Introduce `o x hx`.

Take `⟨y, ⟨z, rfl⟩, rfl⟩` from `hx`. Use `⟨T ((A o).restrict (h i o) z), ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hTeq]`. Both sides reduce to the same expression. Establish `hTsurj : Function.Surjective T`.

Break down `hs j N hNle hNinv with hN0 | hNj` into its components or cases. It suffices to derive a contradiction. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hVi`. Establish `hmem : ((T ⟨x, hx⟩ : V j) : W) ∈ N` using `⟨T ⟨x, hx⟩, ⟨_, rfl⟩, rfl⟩`. Rewrite `hmem` using `[hN0, Submodule.mem_bot]`.

Establish `: T ⟨x, hx⟩ = T 0` using `by rw [map_zero]; exact Subtype.ext hmem`. Conclude with `hx0 (congrArg Subtype.val (hTinj this))`. Introduce `y`. Establish `hy : (y : W) ∈ N` using `by rw [hNj]; exact y.2`. Take `⟨y', ⟨z, rfl⟩, hz⟩` from `hy`.

Conclude with `⟨z, Subtype.ext hz⟩`. Conclude with `hn i j hij ⟨LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩, hTeq⟩`. Rewrite using `[iSupIndep_iff_supIndep]`. Introduce `t u _ i _ hiu`. Conclude with `key u i hiu`.
-/
theorem UpperTheory.V.Lit.Bor.indepAbs :
    UpperTheory.V.Lit.Bor.IndepAbs := by
  classical
  intro O W _ _ A s V h hs hn
  have hsup : ∀ P Q : Submodule ℂ W, (∀ o, ∀ x ∈ P, A o x ∈ P) → (∀ o, ∀ x ∈ Q, A o x ∈ Q) →
      ∀ o, ∀ x ∈ P ⊔ Q, A o x ∈ P ⊔ Q := by
    intro P Q hP hQ o x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (hP o y hy) (hQ o z hz)
  have hfs : ∀ t : Finset (Fin s), ∀ o, ∀ x ∈ t.sup V, A o x ∈ t.sup V := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro o x hx
      simp only [Finset.sup_empty, Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]
    | insert j t hj ih =>
      rw [Finset.sup_insert]
      exact hsup _ _ (h j) ih
  have key : ∀ t : Finset (Fin s), ∀ i, i ∉ t → Disjoint (V i) (t.sup V) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro i _; simp
    | insert j t hj ih =>
      intro i hi
      rw [Finset.mem_insert, not_or] at hi
      obtain ⟨hij, hit⟩ := hi
      have hSinv := hfs t
      have hiS := ih i hit
      have hjS := ih j hj
      rw [Finset.sup_insert, disjoint_iff]
      set S := t.sup V with hSdef
      by_cases hVi : V i = ⊥
      · rw [hVi, bot_inf_eq]
      have hM : ∀ o, ∀ x ∈ V i ⊓ (V j ⊔ S), A o x ∈ V i ⊓ (V j ⊔ S) :=
        fun o x hx => ⟨h i o x hx.1, hsup _ _ (h j) hSinv o x hx.2⟩
      rcases hs i _ inf_le_left hM with hbot | htop
      · exact hbot
      exfalso
      have hle : V i ≤ V j ⊔ S := inf_eq_left.mp htop
      have huniq : ∀ y y' : V j, ((y : W) - y') ∈ S → y = y' := by
        intro y y' hyy
        have h0 : ((y : W) - y') ∈ V j ⊓ S := ⟨sub_mem y.2 y'.2, hyy⟩
        rw [disjoint_iff.mp hjS, Submodule.mem_bot, sub_eq_zero] at h0
        exact Subtype.ext h0
      let fj : V j →ₗ[ℂ] W ⧸ S := S.mkQ ∘ₗ (V j).subtype
      have hfj : Function.Injective fj := by
        intro a b hab
        exact huniq a b ((Submodule.Quotient.eq S).mp hab)
      let ej := LinearEquiv.ofInjective fj hfj
      let fi : V i →ₗ[ℂ] W ⧸ S := S.mkQ ∘ₗ (V i).subtype
      have hrange : ∀ x : V i, fi x ∈ LinearMap.range fj := by
        intro x
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hle x.2)
        refine ⟨⟨y, hy⟩, ?_⟩
        show S.mkQ y = S.mkQ x
        rw [← hyz, map_add, Submodule.mkQ_apply S z, (Submodule.Quotient.mk_eq_zero S).mpr hz,
          add_zero]
      let T : V i →ₗ[ℂ] V j := ej.symm.toLinearMap ∘ₗ (fi.codRestrict (LinearMap.range fj) hrange)
      have hT : ∀ x : V i, ((T x : W) - x) ∈ S := by
        intro x
        have e0 : T x = ej.symm ⟨fi x, hrange x⟩ := rfl
        have e1 := ej.apply_symm_apply ⟨fi x, hrange x⟩
        rw [Subtype.ext_iff, LinearEquiv.ofInjective_apply, ← e0] at e1
        exact (Submodule.Quotient.eq S).mp e1
      have hTeq : ∀ o (x : V i), T ((A o).restrict (h i o) x) = (A o).restrict (h j o) (T x) := by
        intro o x
        apply huniq
        have e1 := hT ((A o).restrict (h i o) x)
        have e2 : A o ((T x : W) - x) ∈ S := hSinv o _ (hT x)
        have e3 : ((T ((A o).restrict (h i o) x) : W) - ((A o).restrict (h j o) (T x) : W))
            = ((T ((A o).restrict (h i o) x) : W) - ((A o).restrict (h i o) x : W))
              - A o ((T x : W) - x) := by
          simp only [LinearMap.restrict_coe_apply, map_sub]
          abel
        rw [e3]
        exact sub_mem e1 e2
      have hTinj : Function.Injective T := by
        rw [← LinearMap.ker_eq_bot, eq_bot_iff]
        intro x hx
        rw [LinearMap.mem_ker] at hx
        have e1 := hT x
        rw [hx, Submodule.coe_zero, zero_sub] at e1
        have hxS : (x : W) ∈ S := by simpa using S.neg_mem e1
        have e2 : (x : W) ∈ V i ⊓ S := ⟨x.2, hxS⟩
        rw [disjoint_iff.mp hiS, Submodule.mem_bot] at e2
        exact (Submodule.mem_bot ℂ).mpr (Subtype.ext e2)
      let N := (LinearMap.range T).map (V j).subtype
      have hNle : N ≤ V j := Submodule.map_subtype_le _ _
      have hNinv : ∀ o, ∀ x ∈ N, A o x ∈ N := by
        intro o x hx
        obtain ⟨y, ⟨z, rfl⟩, rfl⟩ := hx
        refine ⟨T ((A o).restrict (h i o) z), ⟨_, rfl⟩, ?_⟩
        rw [hTeq]
        rfl
      have hTsurj : Function.Surjective T := by
        rcases hs j N hNle hNinv with hN0 | hNj
        · exfalso
          obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVi
          have hmem : ((T ⟨x, hx⟩ : V j) : W) ∈ N := ⟨T ⟨x, hx⟩, ⟨_, rfl⟩, rfl⟩
          rw [hN0, Submodule.mem_bot] at hmem
          have : T ⟨x, hx⟩ = T 0 := by rw [map_zero]; exact Subtype.ext hmem
          exact hx0 (congrArg Subtype.val (hTinj this))
        · intro y
          have hy : (y : W) ∈ N := by rw [hNj]; exact y.2
          obtain ⟨y', ⟨z, rfl⟩, hz⟩ := hy
          exact ⟨z, Subtype.ext hz⟩
      exact hn i j hij ⟨LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩, hTeq⟩
  rw [iSupIndep_iff_supIndep]
  intro t u _ i _ hiu
  exact key u i hiu
