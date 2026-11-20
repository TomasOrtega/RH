import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.ValuedAtFin

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L]

def evF (v : HeightOneSpectrum (𝓞 L)) : Ideles L →* (v.adicCompletion L)ˣ :=
  Units.map
    { toFun := fun x : AdeleRing (𝓞 L) L => x.2 v
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

def evI (w : InfinitePlace L) : Ideles L →* (w.Completion)ˣ :=
  Units.map
    { toFun := fun x : AdeleRing (𝓞 L) L => x.1 w
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evF_val (v : HeightOneSpectrum (𝓞 L)) (x : Ideles L) :
    ((evF v x : (v.adicCompletion L)ˣ) : v.adicCompletion L) = (x : AdeleRing (𝓞 L) L).2 v := rfl

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem evF_diag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : evF v (diagUnits L k) = atFin v k :=
  Units.ext rfl

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem evI_diag (w : InfinitePlace L) (k : Lˣ) : evI w (diagUnits L k) = atInf w k :=
  Units.ext rfl

/- English proof (translation)
The claim follows from `Units.ext (infIdele_snd L w x v)`.
-/
theorem evF_infIdele (v : HeightOneSpectrum (𝓞 L)) (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    evF v (infIdele L w x) = 1 :=
  Units.ext (infIdele_snd L w x v)

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem evI_localIdele (w : InfinitePlace L) (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    evI w (localIdele L v x) = 1 :=
  Units.ext rfl

/- English proof (translation)
The proof uses `by classical exact Units.ext (RestrictedProduct.mulSingle_eq_of_ne (fun u : HeightOneSpectrum (𝓞 L) => u.adicCompletionIntegers L) (x : v.adicCompletion L) h)`.
-/
theorem evF_localIdele_ne (w v : HeightOneSpectrum (𝓞 L)) (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    evF w (localIdele L v x) = 1 :=
  by classical exact Units.ext (RestrictedProduct.mulSingle_eq_of_ne
    (fun u : HeightOneSpectrum (𝓞 L) => u.adicCompletionIntegers L) (x : v.adicCompletion L) h)

/- English proof (translation)
The claim follows from `Units.ext (localIdele_snd_self L v x)`.
-/
theorem evF_localIdele_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    evF v (localIdele L v x) = x :=
  Units.ext (localIdele_snd_self L v x)

/- English proof (translation)
The claim follows from `Units.ext (infIdele_fst_ne L w w' h x)`.
-/
theorem evI_infIdele_ne (w w' : InfinitePlace L) (h : w' ≠ w) (x : (w.Completion)ˣ) :
    evI w' (infIdele L w x) = 1 :=
  Units.ext (infIdele_fst_ne L w w' h x)

/- English proof (translation)
The claim follows from `Units.ext (infIdele_fst_self L w x)`.
-/
theorem evI_infIdele_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    evI w (infIdele L w x) = x :=
  Units.ext (infIdele_fst_self L w x)

/- English proof (translation)
Rewrite using `[infDiag, MonoidHom.finsetProd_apply, map_prod, Finset.prod_eq_single w]`. Conclude with `evI_infIdele_self w _`. Introduce `w' _ hw'`. Conclude with `evI_infIdele_ne w' w (Ne.symm hw') _`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem evI_infDiag (w : InfinitePlace L) (k : Lˣ) : evI w (infDiag k) = atInf w k := by
  rw [infDiag, MonoidHom.finsetProd_apply, map_prod, Finset.prod_eq_single w]
  · exact evI_infIdele_self w _
  · intro w' _ hw'
    exact evI_infIdele_ne w' w (Ne.symm hw') _
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite using `[infDiag, MonoidHom.finsetProd_apply, map_prod]`. Conclude with `Finset.prod_eq_one fun w _ => evF_infIdele v w _`.
-/
theorem evF_infDiag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : evF v (infDiag k) = 1 := by
  rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => evF_infIdele v w _

/- English proof (translation)
Introduce `k T hT`. Use `set D := infDiag k * (∏ v ∈ T, localIdele L v (atFin v k)) with hD`. Use `⟨D⁻¹ * diagUnits L k, ⟨?_, fun v => ?_⟩, by rw [mul_inv_cancel_left]⟩` and prove the remaining obligations. Use function extensionality and compare the values at `w show ((evI w (D⁻¹ * diagUnits L k) : (w.Completion)ˣ) : w.Completion) = (1 : InfiniteAdeleRing L) w`. Establish `hP : evI w (∏ v ∈ T, localIdele L v (atFin v k)) = 1`.

Rewrite using `[map_prod]`. Conclude with `Finset.prod_eq_one fun v _ => evI_localIdele w v _`. Rewrite using `[map_mul, map_inv, hD, map_mul, hP, evI_infDiag, evI_diag, mul_one, inv_mul_cancel]`. Both sides reduce to the same expression. Use `show Valued.v ((evF v (D⁻¹ * diagUnits L k) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1`.

Establish `hP : evF v (∏ u ∈ T, localIdele L u (atFin u k)) = if v ∈ T then atFin v k else 1`. Rewrite using `[map_prod]`. Use `split_ifs with hv`. Rewrite using `[Finset.prod_eq_single v (fun u _ hu => evF_localIdele_ne v u (Ne.symm hu) _) (fun h => absurd hv h), evF_localIdele_self]`. Conclude with `Finset.prod_eq_one fun u hu => evF_localIdele_ne v u (by rintro rfl; exact hv hu) _`.

Rewrite using `[map_mul, map_inv, hD, map_mul, hP, evF_infDiag, evF_diag, one_mul]`. Use `split_ifs with hv`. Rewrite using `[inv_mul_cancel]`. Simplify using the standard rewrite rules. Rewrite using `[inv_one, one_mul, valued_atFin, hT v hv]`.

Simplify using the standard rewrite rules.
-/
theorem decomp : Decomp L := by
  classical
  intro k T hT
  set D := infDiag k * (∏ v ∈ T, localIdele L v (atFin v k)) with hD
  refine ⟨D⁻¹ * diagUnits L k, ⟨?_, fun v => ?_⟩, by rw [mul_inv_cancel_left]⟩
  · funext w
    show ((evI w (D⁻¹ * diagUnits L k) : (w.Completion)ˣ) : w.Completion) = (1 : InfiniteAdeleRing L) w
    have hP : evI w (∏ v ∈ T, localIdele L v (atFin v k)) = 1 := by
      rw [map_prod]
      exact Finset.prod_eq_one fun v _ => evI_localIdele w v _
    rw [map_mul, map_inv, hD, map_mul, hP, evI_infDiag, evI_diag, mul_one, inv_mul_cancel]
    rfl
  · show Valued.v ((evF v (D⁻¹ * diagUnits L k) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1
    have hP : evF v (∏ u ∈ T, localIdele L u (atFin u k)) = if v ∈ T then atFin v k else 1 := by
      rw [map_prod]
      split_ifs with hv
      · rw [Finset.prod_eq_single v (fun u _ hu => evF_localIdele_ne v u (Ne.symm hu) _)
          (fun h => absurd hv h), evF_localIdele_self]
      · exact Finset.prod_eq_one fun u hu => evF_localIdele_ne v u (by rintro rfl; exact hv hu) _
    rw [map_mul, map_inv, hD, map_mul, hP, evF_infDiag, evF_diag, one_mul]
    split_ifs with hv
    · rw [inv_mul_cancel]
      simp
    · rw [inv_one, one_mul, valued_atFin, hT v hv]
      simp

end PI.AlgValsFin.W
