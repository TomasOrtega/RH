import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.IsoOfTrace

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Alg.Jcnil

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Alg

variable (k : Type) [Field k] [CharZero k]

/- English proof (translation)
Introduce `n x`. Take `⟨N, -, S, hS, hN, hSs, hx⟩` from `Module.End.exists_isNilpotent_isSemisimple (K := k) (f := Matrix.toLin' x)`. Establish `hsx : Matrix.toLinAlgEquiv' (Matrix.toLinAlgEquiv'.symm S) = S` using `AlgEquiv.apply_symm_apply _ _`. Use `⟨Matrix.toLinAlgEquiv'.symm S, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hmap` using `AlgHom.map_adjoin (Matrix.toLinAlgEquiv'.symm : _ ≃ₐ[k] Matrix (Fin n) (Fin n) k).toAlgHom {Matrix.toLin' x}`.

Rewrite `hmap` using `[Set.image_singleton]`. Establish `hx' : (Matrix.toLinAlgEquiv'.symm : _ ≃ₐ[k] Matrix (Fin n) (Fin n) k).toAlgHom (Matrix.toLin' x) = x` using `Matrix.toLinAlgEquiv'.symm_apply_apply x`. Rewrite `hmap` using `[hx']`. Rewrite using `[← hmap]`. Conclude with `Subalgebra.mem_map.mpr ⟨S, hS, rfl⟩`.

Establish `: Matrix.toLin' (Matrix.toLinAlgEquiv'.symm S) = S` using `hsx`. Rewrite using `[this]`. Conclude with `hSs`. Establish `hdiff : x - Matrix.toLinAlgEquiv'.symm S = Matrix.toLinAlgEquiv'.symm N`. Apply `Matrix.toLinAlgEquiv'.injective` to reduce the goal to its premises.

Rewrite using `[map_sub, hsx, AlgEquiv.apply_symm_apply]`. Establish `: Matrix.toLinAlgEquiv' x = Matrix.toLin' x` using `rfl`. Rewrite using `[this, hx]`. Normalize the expressions using the abelian group laws. Rewrite using `[hdiff]`.

Conclude with `hN.map _`.
-/
theorem jc : JC k := by
  intro n x
  obtain ⟨N, -, S, hS, hN, hSs, hx⟩ := Module.End.exists_isNilpotent_isSemisimple (K := k) (f := Matrix.toLin' x)
  have hsx : Matrix.toLinAlgEquiv' (Matrix.toLinAlgEquiv'.symm S) = S := AlgEquiv.apply_symm_apply _ _
  refine ⟨Matrix.toLinAlgEquiv'.symm S, ?_, ?_, ?_⟩
  · have hmap := AlgHom.map_adjoin (Matrix.toLinAlgEquiv'.symm : _ ≃ₐ[k] Matrix (Fin n) (Fin n) k).toAlgHom {Matrix.toLin' x}
    rw [Set.image_singleton] at hmap
    have hx' : (Matrix.toLinAlgEquiv'.symm : _ ≃ₐ[k] Matrix (Fin n) (Fin n) k).toAlgHom (Matrix.toLin' x) = x :=
      Matrix.toLinAlgEquiv'.symm_apply_apply x
    rw [hx'] at hmap
    rw [← hmap]
    exact Subalgebra.mem_map.mpr ⟨S, hS, rfl⟩
  · have : Matrix.toLin' (Matrix.toLinAlgEquiv'.symm S) = S := hsx
    rw [this]
    exact hSs
  · have hdiff : x - Matrix.toLinAlgEquiv'.symm S = Matrix.toLinAlgEquiv'.symm N := by
      apply Matrix.toLinAlgEquiv'.injective
      rw [map_sub, hsx, AlgEquiv.apply_symm_apply]
      have : Matrix.toLinAlgEquiv' x = Matrix.toLin' x := rfl
      rw [this, hx]
      abel
    rw [hdiff]
    exact hN.map _

/- English proof (translation)
Introduce `n x s z hs hn hz j`. Establish `hxs : Commute x s` using `Algebra.commute_of_mem_adjoin_self hs`. Establish `hzs : Commute z s` using `Algebra.commute_of_mem_adjoin_singleton_of_commute hs hz`. Establish `hdx : Commute (x - s) x` using `(Commute.refl x).sub_left hxs.symm`. Establish `hds : Commute (x - s) s` using `hxs.sub_left (Commute.refl s)`.

Establish `hg` using `hxs.mul_geom_sum₂ j`. Establish `hc : Commute (x - s) (∑ i ∈ Finset.range j, x ^ i * s ^ (j - 1 - i))` using `Commute.sum_right _ _ _ fun i _ => (hdx.pow_right i).mul_right (hds.pow_right _)`. Establish `hzd : Commute z (x - s)` using `hz.sub_right hzs`. Establish `hnil : IsNilpotent (z * x ^ j - z * s ^ j)`. Rewrite using `[← mul_sub, ← hg, ← mul_assoc, hzd.eq, mul_assoc]`.

Conclude with `Commute.isNilpotent_mul_right (hzd.symm.mul_right hc) hn`. Establish `ht` using `Matrix.isNilpotent_trace_of_isNilpotent hnil`. Rewrite `ht` using `[Matrix.trace_sub]`. Conclude with `sub_eq_zero.mp ht.eq_zero`.
-/
theorem trNil : TrNil k := by
  intro n x s z hs hn hz j
  have hxs : Commute x s := Algebra.commute_of_mem_adjoin_self hs
  have hzs : Commute z s := Algebra.commute_of_mem_adjoin_singleton_of_commute hs hz
  have hdx : Commute (x - s) x := (Commute.refl x).sub_left hxs.symm
  have hds : Commute (x - s) s := hxs.sub_left (Commute.refl s)
  have hg := hxs.mul_geom_sum₂ j
  have hc : Commute (x - s) (∑ i ∈ Finset.range j, x ^ i * s ^ (j - 1 - i)) :=
    Commute.sum_right _ _ _ fun i _ => (hdx.pow_right i).mul_right (hds.pow_right _)
  have hzd : Commute z (x - s) := hz.sub_right hzs
  have hnil : IsNilpotent (z * x ^ j - z * s ^ j) := by
    rw [← mul_sub, ← hg, ← mul_assoc, hzd.eq, mul_assoc]
    exact Commute.isNilpotent_mul_right (hzd.symm.mul_right hc) hn
  have ht := Matrix.isNilpotent_trace_of_isNilpotent hnil
  rw [Matrix.trace_sub] at ht
  exact sub_eq_zero.mp ht.eq_zero

end PositivityTheory.RgUd.T.Alg.Jcnil
