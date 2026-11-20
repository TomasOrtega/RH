import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `k _ _ _ _ N V _ _ π r s d e j d' e' t c f hord hsub`. Establish `hKf : twKer π (unipRad k f) 1 = ⊤` using `Submodule.Quotient.subsingleton_iff.mp hsub`. Apply `Submodule.Quotient.subsingleton_iff.mpr` to reduce the goal to its premises. Establish `hfblk : ∀ (a : Fin t) (i : Fin (c a)), blk f (f ⟨a, i⟩) = a` using `fun a i => by simp only [blk, Equiv.symm_apply_apply]`. Establish `heblk : ∀ (a : Fin r) (i : Fin (d a)), blk e (e ⟨a, i⟩) = a` using `fun a i => by simp only [blk, Equiv.symm_apply_apply]`.

Establish `he'blk : ∀ (b : Fin s) (i : Fin (d' b)), blk e' (e' ⟨b, i⟩) = b` using `fun b i => by simp only [blk, Equiv.symm_apply_apply]`. It suffices to establish `key : twKer π (unipRad k f) 1 ≤ (twKer ((jac e π).comp (MonoidHom.mulSingle (fun a => GL (Fin (d a)) k) j)) (unipRad k e') 1).comap (twKer π (unipRad k e) 1).mkQ by`. Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Conclude with `key (hKf ▸ Submodule.mem_top)`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨n, hn⟩, w, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap]`. Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul]`.

Take `⟨hnf, hnd⟩` from `mem_unipRad.mp hn`. Establish `hoff : ∀ p q, p ≠ q → (n : Matrix (Fin N) (Fin N) k) p q ≠ 0 → blk f p < blk f q`. Introduce `p q hpq h0`. Break down `lt_trichotomy (blk f p) (blk f q) with h | h | h` into its components or cases. Conclude with `h`.

It suffices to derive a contradiction. Take `⟨⟨a, i⟩, rfl⟩` from `f.surjective p`. Take `⟨⟨b, i'⟩, rfl⟩` from `f.surjective q`. Rewrite `h` using `[hfblk, hfblk]`. Substitute `h` using the available equality.

Rewrite `h0` using `[hnd a i i']`. Establish `hii : i = i'`. Assume the negation of the conclusion as `hii`. Conclude with `h0 (Matrix.one_apply_ne hii)`. Conclude with `hpq (by rw [hii])`.

Conclude with `absurd (mem_parab.mp hnf p q h) h0`. Establish `hdiag : ∀ p, (n : Matrix (Fin N) (Fin N) k) p p = 1`. Introduce `p`. Take `⟨⟨a, i⟩, rfl⟩` from `f.surjective p`. Rewrite using `[hnd a i i, Matrix.one_apply_eq]`.

Establish `hA : n ∈ parab k e`. Rewrite using `[mem_parab]`. Introduce `p q hlt`. Assume the negation of the conclusion as `h0`. Establish `hpq : p ≠ q` using `fun h => by`.

Substitute `h` using the available equality. Conclude with `lt_irrefl _ hlt`. Break down `hord p q (hoff p q hpq h0) with h | ⟨p', q', rfl, rfl, -⟩` into its components or cases. Conclude with `lt_asymm h hlt`. Rewrite `hlt` using `[heblk, heblk]`.

Conclude with `lt_irrefl _ hlt`. Take `⟨u', hu'eq⟩ : ∃ u', leviProj k e ⟨n, hA⟩ j = u'` from `⟨_, rfl⟩`. Establish `hu'e : ∀ i i', (u' : Matrix (Fin (d j)) (Fin (d j)) k) i i' = (n : Matrix (Fin N) (Fin N) k) (e ⟨j, i⟩) (e ⟨j, i'⟩)`. Introduce `i i'`. Rewrite using `[← hu'eq, leviProj_apply]`.

Establish `hu' : u' ∈ unipRad k e'`. Rewrite using `[mem_unipRad]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_parab]`. Introduce `i i' hlt`.

Rewrite using `[hu'e]`. Assume the negation of the conclusion as `h0`. Establish `hii : i ≠ i'` using `fun h => by`. Substitute `h` using the available equality. Conclude with `lt_irrefl _ hlt`.

Establish `hpq : e ⟨j, i⟩ ≠ e ⟨j, i'⟩` using `fun h => hii (by simpa using e.injective h)`. Break down `hord _ _ (hoff _ _ hpq h0) with h | ⟨p', q', h1, h2, h3⟩` into its components or cases. Rewrite `h` using `[heblk, heblk]`. Conclude with `lt_irrefl _ h`. Take `rfl : i = p'` from `by simpa using e.injective h1`.

Take `rfl : i' = q'` from `by simpa using e.injective h2`. Conclude with `lt_asymm h3 hlt`. Introduce `b x y`. Rewrite using `[hu'e]`. Distinguish the cases in `hxy : x = y`.

Substitute `hxy` using the available equality. Rewrite using `[hdiag, Matrix.one_apply_eq]`. Rewrite using `[Matrix.one_apply_ne hxy]`. Assume the negation of the conclusion as `h0`. Establish `hpq : e ⟨j, e' ⟨b, x⟩⟩ ≠ e ⟨j, e' ⟨b, y⟩⟩` using `fun h => hxy (by simpa using e.injective h)`.

Break down `hord _ _ (hoff _ _ hpq h0) with h | ⟨p', q', h1, h2, h3⟩` into its components or cases. Rewrite `h` using `[heblk, heblk]`. Conclude with `lt_irrefl _ h`. Take `rfl : e' ⟨b, x⟩ = p'` from `by simpa using e.injective h1`. Take `rfl : e' ⟨b, y⟩ = q'` from `by simpa using e.injective h2`.

Rewrite `h3` using `[he'blk, he'blk]`. Conclude with `lt_irrefl _ h3`. Establish `hproj : leviProj k e ⟨n, hA⟩ = Pi.mulSingle j u'`. Use function extensionality and compare the values at `a`. Distinguish the cases in `ha : a = j`.

Substitute `ha` using the available equality. Rewrite using `[Pi.mulSingle_eq_same, hu'eq]`. Rewrite using `[Pi.mulSingle_eq_of_ne ha]`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i i'`.

Rewrite using `[leviProj_apply, Units.val_one]`. Distinguish the cases in `hii : i = i'`. Substitute `hii` using the available equality. Rewrite using `[hdiag, Matrix.one_apply_eq]`. Rewrite using `[Matrix.one_apply_ne hii]`.

Assume the negation of the conclusion as `h0`. Establish `hpq : e ⟨a, i⟩ ≠ e ⟨a, i'⟩` using `fun h => hii (by simpa using e.injective h)`. Break down `hord _ _ (hoff _ _ hpq h0) with h | ⟨p', q', h1, -, -⟩` into its components or cases. Rewrite `h` using `[heblk, heblk]`. Conclude with `lt_irrefl _ h`.

Conclude with `ha (congrArg Sigma.fst (e.injective h1))`. Take `⟨L, hLeq⟩ : ∃ L, leviEmb k e (Pi.mulSingle j u') = L` from `⟨_, rfl⟩`. Establish `hLpar : L ∈ parab k e` using `hLeq ▸ leviEmb_mem_parab k e _`. Establish `hLproj : leviProj k e ⟨L, hLpar⟩ = Pi.mulSingle j u'`. Substitute `hLeq` using the available equality.

Conclude with `leviProj_leviEmb k e _`. Establish `hupar : n * L⁻¹ ∈ parab k e` using `mul_mem hA (inv_mem hLpar)`. Establish `huproj : leviProj k e ⟨n * L⁻¹, hupar⟩ = 1`. Establish `hsplit : (⟨n * L⁻¹, hupar⟩ : parab k e) = ⟨n, hA⟩ * (⟨L, hLpar⟩ : parab k e)⁻¹` using `rfl`. Rewrite using `[hsplit, map_mul, map_inv, hproj, hLproj, mul_inv_cancel]`.

Establish `hu : n * L⁻¹ ∈ unipRad k e`. Rewrite using `[mem_unipRad]`. Use `⟨hupar, fun a i i' => ?_⟩` and prove the remaining obligations. Establish `h` using `leviProj_apply k e ⟨n * L⁻¹, hupar⟩ a i i'`. Rewrite `h` using `[huproj]`.

Conclude with `h.symm`. Establish `hdelta : deltaHalf k (fun a => Fin (d a)) (Pi.mulSingle j u') = 1`. Unfold `deltaHalf`. Rewrite using `[MonoidHom.finset_prod_apply]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises.

Introduce `a _`. Rewrite using `[MonoidHom.comp_apply, Pi.evalMonoidHom_apply]`. Unfold `detChar`. Rewrite using `[MonoidHom.comp_apply]`. Establish `hdet : Matrix.GeneralLinearGroup.det ((Pi.mulSingle j u' : Levi k (fun a => Fin (d a))) a) = 1`.

Distinguish the cases in `ha : a = j`. Substitute `ha` using the available equality. Rewrite using `[Pi.mulSingle_eq_same]`. Conclude with `det_eq_one_of_mem_unipRad k hu'`. Rewrite using `[Pi.mulSingle_eq_of_ne ha, map_one]`.

Rewrite using `[hdet, map_one]`. Establish `hsplit : π n w - w = (π (n * L⁻¹) (π L w) - π L w) + (π L w - w)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]`. Normalize the expressions using the abelian group laws. Rewrite using `[hsplit, map_add]`.

Use `add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr]`. Conclude with `zero_mem _`. Conclude with `Submodule.subset_span ⟨⟨n * L⁻¹, hu⟩, π L w, by simp⟩`. Rewrite using `[map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply]`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨⟨u', hu'⟩, Submodule.Quotient.mk w, ?_⟩` and prove the remaining obligations. Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.comp_apply, MonoidHom.mulSingle_apply]`. Rewrite using `[show jac e π = twist (jacU e π) (deltaHalf k (fun a => Fin (d a)))⁻¹ from rfl, twist_apply, MonoidHom.inv_apply, hdelta, inv_one, Units.val_one, one_smul, ← hLeq]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.weilDeligne_unipotent_monodromy :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (r s : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin N) (j : Fin r) (d' : Fin s → ℕ) (e' : (Σ b, Fin (d' b)) ≃ Fin (d j)) (t : ℕ) (c : Fin t → ℕ) (f : (Σ a, Fin (c a)) ≃ Fin N),
    (∀ p q, blk f p < blk f q → (blk e p < blk e q ∨ ∃ p' q', p = e ⟨j, p'⟩ ∧ q = e ⟨j, q'⟩ ∧ blk e' p' < blk e' q')) →
    Subsingleton (Jacquet π (unipRad k f)) →
    Subsingleton (Jacquet ((jac e π).comp (MonoidHom.mulSingle (fun a => GL (Fin (d a)) k) j) :
      Representation ℂ (GL (Fin (d j)) k) (Jacquet π (unipRad k e))) (unipRad k e')) := by
  intro k _ _ _ _ N V _ _ π r s d e j d' e' t c f hord hsub
  classical
  have hKf : twKer π (unipRad k f) 1 = ⊤ := Submodule.Quotient.subsingleton_iff.mp hsub
  apply Submodule.Quotient.subsingleton_iff.mpr
  have hfblk : ∀ (a : Fin t) (i : Fin (c a)), blk f (f ⟨a, i⟩) = a := fun a i => by simp only [blk, Equiv.symm_apply_apply]
  have heblk : ∀ (a : Fin r) (i : Fin (d a)), blk e (e ⟨a, i⟩) = a := fun a i => by simp only [blk, Equiv.symm_apply_apply]
  have he'blk : ∀ (b : Fin s) (i : Fin (d' b)), blk e' (e' ⟨b, i⟩) = b := fun b i => by simp only [blk, Equiv.symm_apply_apply]
  suffices key : twKer π (unipRad k f) 1 ≤
      (twKer ((jac e π).comp (MonoidHom.mulSingle (fun a => GL (Fin (d a)) k) j))
        (unipRad k e') 1).comap (twKer π (unipRad k e) 1).mkQ by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact key (hKf ▸ Submodule.mem_top)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨n, hn⟩, w, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  obtain ⟨hnf, hnd⟩ := mem_unipRad.mp hn
  have hoff : ∀ p q, p ≠ q → (n : Matrix (Fin N) (Fin N) k) p q ≠ 0 → blk f p < blk f q := by
    intro p q hpq h0
    rcases lt_trichotomy (blk f p) (blk f q) with h | h | h
    · exact h
    · exfalso
      obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective p
      obtain ⟨⟨b, i'⟩, rfl⟩ := f.surjective q
      rw [hfblk, hfblk] at h
      subst h
      rw [hnd a i i'] at h0
      have hii : i = i' := by
        by_contra hii
        exact h0 (Matrix.one_apply_ne hii)
      exact hpq (by rw [hii])
    · exact absurd (mem_parab.mp hnf p q h) h0
  have hdiag : ∀ p, (n : Matrix (Fin N) (Fin N) k) p p = 1 := by
    intro p
    obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective p
    rw [hnd a i i, Matrix.one_apply_eq]
  have hA : n ∈ parab k e := by
    rw [mem_parab]
    intro p q hlt
    by_contra h0
    have hpq : p ≠ q := fun h => by
      subst h
      exact lt_irrefl _ hlt
    rcases hord p q (hoff p q hpq h0) with h | ⟨p', q', rfl, rfl, -⟩
    · exact lt_asymm h hlt
    · rw [heblk, heblk] at hlt
      exact lt_irrefl _ hlt
  obtain ⟨u', hu'eq⟩ : ∃ u', leviProj k e ⟨n, hA⟩ j = u' := ⟨_, rfl⟩
  have hu'e : ∀ i i', (u' : Matrix (Fin (d j)) (Fin (d j)) k) i i' =
      (n : Matrix (Fin N) (Fin N) k) (e ⟨j, i⟩) (e ⟨j, i'⟩) := by
    intro i i'
    rw [← hu'eq, leviProj_apply]
  have hu' : u' ∈ unipRad k e' := by
    rw [mem_unipRad]
    refine ⟨?_, ?_⟩
    · rw [mem_parab]
      intro i i' hlt
      rw [hu'e]
      by_contra h0
      have hii : i ≠ i' := fun h => by
        subst h
        exact lt_irrefl _ hlt
      have hpq : e ⟨j, i⟩ ≠ e ⟨j, i'⟩ := fun h => hii (by simpa using e.injective h)
      rcases hord _ _ (hoff _ _ hpq h0) with h | ⟨p', q', h1, h2, h3⟩
      · rw [heblk, heblk] at h
        exact lt_irrefl _ h
      · obtain rfl : i = p' := by simpa using e.injective h1
        obtain rfl : i' = q' := by simpa using e.injective h2
        exact lt_asymm h3 hlt
    · intro b x y
      rw [hu'e]
      by_cases hxy : x = y
      · subst hxy
        rw [hdiag, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne hxy]
        by_contra h0
        have hpq : e ⟨j, e' ⟨b, x⟩⟩ ≠ e ⟨j, e' ⟨b, y⟩⟩ := fun h => hxy (by simpa using e.injective h)
        rcases hord _ _ (hoff _ _ hpq h0) with h | ⟨p', q', h1, h2, h3⟩
        · rw [heblk, heblk] at h
          exact lt_irrefl _ h
        · obtain rfl : e' ⟨b, x⟩ = p' := by simpa using e.injective h1
          obtain rfl : e' ⟨b, y⟩ = q' := by simpa using e.injective h2
          rw [he'blk, he'blk] at h3
          exact lt_irrefl _ h3
  have hproj : leviProj k e ⟨n, hA⟩ = Pi.mulSingle j u' := by
    funext a
    by_cases ha : a = j
    · subst ha
      rw [Pi.mulSingle_eq_same, hu'eq]
    · rw [Pi.mulSingle_eq_of_ne ha]
      apply Units.ext
      ext i i'
      rw [leviProj_apply, Units.val_one]
      by_cases hii : i = i'
      · subst hii
        rw [hdiag, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne hii]
        by_contra h0
        have hpq : e ⟨a, i⟩ ≠ e ⟨a, i'⟩ := fun h => hii (by simpa using e.injective h)
        rcases hord _ _ (hoff _ _ hpq h0) with h | ⟨p', q', h1, -, -⟩
        · rw [heblk, heblk] at h
          exact lt_irrefl _ h
        · exact ha (congrArg Sigma.fst (e.injective h1))
  obtain ⟨L, hLeq⟩ : ∃ L, leviEmb k e (Pi.mulSingle j u') = L := ⟨_, rfl⟩
  have hLpar : L ∈ parab k e := hLeq ▸ leviEmb_mem_parab k e _
  have hLproj : leviProj k e ⟨L, hLpar⟩ = Pi.mulSingle j u' := by
    subst hLeq
    exact leviProj_leviEmb k e _
  have hupar : n * L⁻¹ ∈ parab k e := mul_mem hA (inv_mem hLpar)
  have huproj : leviProj k e ⟨n * L⁻¹, hupar⟩ = 1 := by
    have hsplit : (⟨n * L⁻¹, hupar⟩ : parab k e) = ⟨n, hA⟩ * (⟨L, hLpar⟩ : parab k e)⁻¹ := rfl
    rw [hsplit, map_mul, map_inv, hproj, hLproj, mul_inv_cancel]
  have hu : n * L⁻¹ ∈ unipRad k e := by
    rw [mem_unipRad]
    refine ⟨hupar, fun a i i' => ?_⟩
    have h := leviProj_apply k e ⟨n * L⁻¹, hupar⟩ a i i'
    rw [huproj] at h
    exact h.symm
  have hdelta : deltaHalf k (fun a => Fin (d a)) (Pi.mulSingle j u') = 1 := by
    unfold deltaHalf
    rw [MonoidHom.finset_prod_apply]
    apply Finset.prod_eq_one
    intro a _
    rw [MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
    unfold detChar
    rw [MonoidHom.comp_apply]
    have hdet : Matrix.GeneralLinearGroup.det ((Pi.mulSingle j u' : Levi k (fun a => Fin (d a))) a) = 1 := by
      by_cases ha : a = j
      · subst ha
        rw [Pi.mulSingle_eq_same]
        exact det_eq_one_of_mem_unipRad k hu'
      · rw [Pi.mulSingle_eq_of_ne ha, map_one]
    rw [hdet, map_one]
  have hsplit : π n w - w = (π (n * L⁻¹) (π L w) - π L w) + (π L w - w) := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    abel
  rw [hsplit, map_add]
  refine add_mem ?_ ?_
  · rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr]
    · exact zero_mem _
    · exact Submodule.subset_span ⟨⟨n * L⁻¹, hu⟩, π L w, by simp⟩
  · rw [map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply]
    apply Submodule.subset_span
    refine ⟨⟨u', hu'⟩, Submodule.Quotient.mk w, ?_⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.comp_apply, MonoidHom.mulSingle_apply]
    rw [show jac e π = twist (jacU e π) (deltaHalf k (fun a => Fin (d a)))⁻¹ from rfl, twist_apply,
      MonoidHom.inv_apply, hdelta, inv_one, Units.val_one, one_smul, ← hLeq]
    rfl
