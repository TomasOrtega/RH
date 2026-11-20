import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfJacquetMin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.JacMinCuspGL

open GlobalTheory.SmGL.CuspMax GlobalTheory.JacMinCusp Matrix

/- English proof (translation)
Introduce `k _ _ _ _ a b n h V _ _ π hπ hmin`. Use `set J := (jac₂ (stdSum h) π).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin b) k)) with hJdef`. Use `(isCuspidal_iff_maximal k b _ J).2 ⟨isSmooth_comp (isSmooth_jac₂ _ hπ) _ (continuous_const.prodMk continuous_id : Continuous fun x : GL (Fin b) k => ((1 : GL (Fin a) k), x)), fun r t h' hr ht => ?_⟩` and prove the remaining obligations. Establish `hcd : a + r + t = n` using `by omega`. Establish `hJ : twKer π (unipRad k (two (stdSum hcd))) 1 = ⊤` using `Submodule.Quotient.subsingleton_iff.1 (hmin (a + r) t hcd ht (by omega))`.

Use `set Kab := twKer π (unipRad k (two (stdSum h))) 1 with hKab`. Use `set K' := twKer J (unipRad k (two (stdSum h'))) 1 with hK'`. Establish `hB : ∀ g : GL (Fin a) k × GL (Fin b) k, g.1 = 1 → GeneralLinearGroup.det g.2 = 1 → ∀ v : V, jac₂ (stdSum h) π g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π (leviEmb k (two (stdSum h)) (leviTwo k _ _ g)) v)`. Introduce `g h1 h2 v`. Establish `hd : deltaHalf k (Two (Fin a) (Fin b)) (leviTwo k _ _ g) = 1`.

Rewrite using `[deltaHalf_two, h1, h2]`. Simplify using the standard rewrite rules. Use `show jac (two (stdSum h)) π (leviTwo k _ _ g) _ = _`. Rewrite using `[jac_mk, hd]`. Simplify using the standard rewrite rules.

Establish `hN : ∀ u ∈ unipRad k (two (stdSum h)), ∀ v : V, (Submodule.Quotient.mk (π u v) : V ⧸ Kab) = Submodule.Quotient.mk v`. Introduce `u hu v`. Conclude with `(Submodule.Quotient.eq Kab).2 (Submodule.subset_span ⟨⟨u, hu⟩, v, by simp⟩)`. Establish `hC : ∀ u ∈ unipRad k (two (stdSum hcd)), ∀ v : V, (Submodule.Quotient.mk (π u v) : V ⧸ Kab) - Submodule.Quotient.mk v ∈ K'`. Introduce `u hu v`.

Establish `hu'` using `(mem_unipRad_two_iff hcd).1 hu`. Establish `hp : u ∈ parab k (two (stdSum h))`. Rewrite using `[mem_parab]`. Introduce `i j hij`. Rewrite `hij` using `[blk_two_stdSum_lt]`.

Rewrite using `[hu' i j (by omega), Matrix.one_apply_ne]`. Introduce `hij'`. Substitute `hij'` using the available equality. Use linear arithmetic over natural numbers and integers. Take `⟨n', hn', hun⟩` from `exists_levi_mul_unip k (two (stdSum h)) ⟨u, hp⟩`.

Use `set g := (leviTwo k (Fin a) (Fin b)).symm (leviProj k (two (stdSum h)) ⟨u, hp⟩) with hg`. Establish `hlg : leviTwo k _ _ g = leviProj k (two (stdSum h)) ⟨u, hp⟩` using `by simp [g]`. Establish `hg1 : g.1 = 1`. Use extensionality with `i j`. Use `show (leviProj k (two (stdSum h)) ⟨u, hp⟩ false : Matrix (Fin a) (Fin a) k) i j = _`.

Rewrite using `[leviProj_apply, two_false, two_false]`. Rewrite using `[hu' _ _ (by simp; omega)]`. Simplify using `[Matrix.one_apply, stdSum]`. Establish `hg2 : g.2 ∈ unipRad k (two (stdSum h'))`. Rewrite using `[mem_unipRad_two_iff]`.

Introduce `i j hij`. Use `show (leviProj k (two (stdSum h)) ⟨u, hp⟩ true : Matrix (Fin b) (Fin b) k) i j = _`. Rewrite using `[leviProj_apply, two_true, two_true]`. Rewrite using `[hu' _ _ (by simp; omega)]`. Simplify using `[Matrix.one_apply, stdSum]`.

Establish `hdet : GeneralLinearGroup.det g.2 = 1` using `det_eq_one_of_mem_unipRad k hg2`. Establish `hu_eq : u = leviEmb k (two (stdSum h)) (leviTwo k _ _ g) * n'` using `by rw [hlg]; exact hun`. Establish `hJu : J g.2 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π u v)`. Rewrite using `[hu_eq, map_mul, Module.End.mul_apply]`. Use `show jac₂ (stdSum h) π (1, g.2) _ = _`.

Rewrite using `[hB (1, g.2) rfl hdet, show ((1, g.2) : GL (Fin a) k × GL (Fin b) k) = g from Prod.ext hg1.symm rfl]`. Use `(Submodule.Quotient.eq Kab).2 ?_` and prove the remaining obligations. Rewrite using `[← map_sub]`. Use `twKer_le_comap π _ _ (leviEmb_mem_normalizer k _ _) ?_` and prove the remaining obligations. Use `(Submodule.Quotient.eq Kab).1 (hN n' hn' v)` as an intermediate fact.

Rewrite using `[← neg_sub]`. Conclude with `Kab.neg_mem this`. Rewrite using `[← hJu]`. Conclude with `Submodule.subset_span ⟨⟨g.2, hg2⟩, Submodule.Quotient.mk v, by simp⟩`. Use `Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun x _ => ?_)` and prove the remaining obligations.

Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective Kab x`. Establish `hle : twKer π (unipRad k (two (stdSum hcd))) 1 ≤ K'.comap Kab.mkQ`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, w, rfl⟩`. Simplify `hC u u.2 w` using `[Submodule.mkQ_apply]`.

Conclude with `hle (hJ ▸ Submodule.mem_top)`.
-/
theorem isCuspidal_jac₂_inr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b n : ℕ) (h : a + b = n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    (∀ (r t : ℕ) (h' : r + t = n), 0 < t → t < b → Subsingleton (Jacquet π (unipRad k (two (stdSum h'))))) →
    IsCuspidal (k := k) (n := Fin b) ((jac₂ (stdSum h) π).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin b) k))) := by
  intro k _ _ _ _ a b n h V _ _ π hπ hmin
  set J := (jac₂ (stdSum h) π).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin b) k)) with hJdef
  refine (isCuspidal_iff_maximal k b _ J).2 ⟨isSmooth_comp (isSmooth_jac₂ _ hπ) _
    (continuous_const.prodMk continuous_id :
      Continuous fun x : GL (Fin b) k => ((1 : GL (Fin a) k), x)),
    fun r t h' hr ht => ?_⟩
  have hcd : a + r + t = n := by omega
  have hJ : twKer π (unipRad k (two (stdSum hcd))) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 (hmin (a + r) t hcd ht (by omega))
  set Kab := twKer π (unipRad k (two (stdSum h))) 1 with hKab
  set K' := twKer J (unipRad k (two (stdSum h'))) 1 with hK'

  have hB : ∀ g : GL (Fin a) k × GL (Fin b) k, g.1 = 1 → GeneralLinearGroup.det g.2 = 1 → ∀ v : V,
      jac₂ (stdSum h) π g (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk (π (leviEmb k (two (stdSum h)) (leviTwo k _ _ g)) v) := by
    intro g h1 h2 v
    have hd : deltaHalf k (Two (Fin a) (Fin b)) (leviTwo k _ _ g) = 1 := by
      rw [deltaHalf_two, h1, h2]; simp
    show jac (two (stdSum h)) π (leviTwo k _ _ g) _ = _
    rw [jac_mk, hd]; simp
  have hN : ∀ u ∈ unipRad k (two (stdSum h)), ∀ v : V,
      (Submodule.Quotient.mk (π u v) : V ⧸ Kab) = Submodule.Quotient.mk v := by
    intro u hu v
    exact (Submodule.Quotient.eq Kab).2 (Submodule.subset_span ⟨⟨u, hu⟩, v, by simp⟩)

  have hC : ∀ u ∈ unipRad k (two (stdSum hcd)), ∀ v : V,
      (Submodule.Quotient.mk (π u v) : V ⧸ Kab) - Submodule.Quotient.mk v ∈ K' := by
    intro u hu v
    have hu' := (mem_unipRad_two_iff hcd).1 hu
    have hp : u ∈ parab k (two (stdSum h)) := by
      rw [mem_parab]
      intro i j hij
      rw [blk_two_stdSum_lt] at hij
      rw [hu' i j (by omega), Matrix.one_apply_ne]
      intro hij'; subst hij'; omega
    obtain ⟨n', hn', hun⟩ := exists_levi_mul_unip k (two (stdSum h)) ⟨u, hp⟩
    set g := (leviTwo k (Fin a) (Fin b)).symm (leviProj k (two (stdSum h)) ⟨u, hp⟩) with hg
    have hlg : leviTwo k _ _ g = leviProj k (two (stdSum h)) ⟨u, hp⟩ := by simp [g]
    have hg1 : g.1 = 1 := by
      ext i j
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ false : Matrix (Fin a) (Fin a) k) i j = _
      rw [leviProj_apply, two_false, two_false]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hg2 : g.2 ∈ unipRad k (two (stdSum h')) := by
      rw [mem_unipRad_two_iff]
      intro i j hij
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ true : Matrix (Fin b) (Fin b) k) i j = _
      rw [leviProj_apply, two_true, two_true]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hdet : GeneralLinearGroup.det g.2 = 1 := det_eq_one_of_mem_unipRad k hg2
    have hu_eq : u = leviEmb k (two (stdSum h)) (leviTwo k _ _ g) * n' := by rw [hlg]; exact hun
    have hJu : J g.2 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π u v) := by
      rw [hu_eq, map_mul, Module.End.mul_apply]
      show jac₂ (stdSum h) π (1, g.2) _ = _
      rw [hB (1, g.2) rfl hdet, show ((1, g.2) : GL (Fin a) k × GL (Fin b) k) = g from Prod.ext hg1.symm rfl]
      refine (Submodule.Quotient.eq Kab).2 ?_
      rw [← map_sub]
      refine twKer_le_comap π _ _ (leviEmb_mem_normalizer k _ _) ?_
      have := (Submodule.Quotient.eq Kab).1 (hN n' hn' v)
      rw [← neg_sub]
      exact Kab.neg_mem this
    rw [← hJu]
    exact Submodule.subset_span ⟨⟨g.2, hg2⟩, Submodule.Quotient.mk v, by simp⟩
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun x _ => ?_)
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective Kab x
  have hle : twKer π (unipRad k (two (stdSum hcd))) 1 ≤ K'.comap Kab.mkQ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, w, rfl⟩
    simpa [Submodule.mkQ_apply] using hC u u.2 w
  exact hle (hJ ▸ Submodule.mem_top)

end GlobalTheory.JacMinCuspGL
