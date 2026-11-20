import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeAdelicMatrixIntegralTranslate

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

/- English proof (translation)
Rewrite using `[← GlobalTheory.AdelicMatLat.algebraMap_mem_iff, GlobalTheory.AdelicMatLat.mem_intAdeles, Ohat, Subring.mem_iInf]`. Both sides reduce to the same expression.
-/
private theorem alg_mem_Ohat {F : Type} [Field F] [NumberField F] (x : F) :
    algebraMap F (Af F) x ∈ Ohat F ↔ ∃ r : 𝓞 F, (r : F) = x := by
  rw [← GlobalTheory.AdelicMatLat.algebraMap_mem_iff, GlobalTheory.AdelicMatLat.mem_intAdeles, Ohat, Subring.mem_iInf]
  rfl

/- English proof (translation)
Introduce `F _ _ n`. Use extensionality with `g`. Rewrite using `[Subgroup.mem_comap, mem_KLev]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ha, hb, -⟩`.

Rewrite `hb` using `[← map_inv]`. Establish `ha' : ∀ a b, ∃ r : 𝓞 F, (r : F) = g a b` using `fun a b => (alg_mem_Ohat _).1 (ha a b)`. Establish `hb' : ∀ a b, ∃ r : 𝓞 F, (r : F) = (g⁻¹ : GL (Fin n) F) a b` using `fun a b => (alg_mem_Ohat _).1 (hb a b)`. Use `choose A hA using ha'`. Use `choose B hB using hb'`.

Establish `inj : Function.Injective (RingHom.mapMatrix (m` using `Fin n) (algebraMap (𝓞 F) F)) := fun x y h => Matrix.ext fun a b => IsFractionRing.injective (𝓞 F) F (congrFun (congrFun h a) b)`. Establish `eA : RingHom.mapMatrix (m` using `Fin n) (algebraMap (𝓞 F) F) (Matrix.of A) = g.val := Matrix.ext fun a b => hA a b`. Establish `eB : RingHom.mapMatrix (m` using `Fin n) (algebraMap (𝓞 F) F) (Matrix.of B) = (g⁻¹).val := Matrix.ext fun a b => hB a b`. Use `⟨⟨Matrix.of A, Matrix.of B, inj ?_, inj ?_⟩, Units.ext eA⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_one, eA, eB]`.

Conclude with `g.mul_inv`. Rewrite using `[map_mul, map_one, eA, eB]`. Conclude with `g.inv_mul`. Introduce and unpack `⟨k, rfl⟩`. Establish `h1 : ∀ (k : GL (Fin n) (𝓞 F)) a b, (CohB.ratAf F n (Matrix.GeneralLinearGroup.map (n` using `Fin n) (algebraMap (𝓞 F) F) k)) a b ∈ Ohat F := fun k a b => (alg_mem_Ohat _).2 ⟨k a b, rfl⟩`.

Use `⟨h1 k, fun a b => ?_, fun a b => ⟨_, ?_, by rw [Nat.cast_one]; exact (one_mul _).symm⟩⟩` and prove the remaining obligations. Rewrite using `[← map_inv, ← map_inv]`. Conclude with `h1 _ a b`. Use `sub_mem (h1 k a b) ?_` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`.

Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.
-/
theorem UpperTheory.arithmetic_subgroup_level_one :
    UpperTheory.V.Af.CohB.ArithOne := by
  intro F _ _ n
  ext g
  rw [Subgroup.mem_comap, mem_KLev]
  constructor
  · rintro ⟨ha, hb, -⟩
    rw [← map_inv] at hb
    have ha' : ∀ a b, ∃ r : 𝓞 F, (r : F) = g a b := fun a b => (alg_mem_Ohat _).1 (ha a b)
    have hb' : ∀ a b, ∃ r : 𝓞 F, (r : F) = (g⁻¹ : GL (Fin n) F) a b := fun a b => (alg_mem_Ohat _).1 (hb a b)
    choose A hA using ha'
    choose B hB using hb'
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) (algebraMap (𝓞 F) F)) := fun x y h =>
      Matrix.ext fun a b => IsFractionRing.injective (𝓞 F) F (congrFun (congrFun h a) b)
    have eA : RingHom.mapMatrix (m := Fin n) (algebraMap (𝓞 F) F) (Matrix.of A) = g.val :=
      Matrix.ext fun a b => hA a b
    have eB : RingHom.mapMatrix (m := Fin n) (algebraMap (𝓞 F) F) (Matrix.of B) = (g⁻¹).val :=
      Matrix.ext fun a b => hB a b
    refine ⟨⟨Matrix.of A, Matrix.of B, inj ?_, inj ?_⟩, Units.ext eA⟩
    · rw [map_mul, map_one, eA, eB]; exact g.mul_inv
    · rw [map_mul, map_one, eA, eB]; exact g.inv_mul
  · rintro ⟨k, rfl⟩
    have h1 : ∀ (k : GL (Fin n) (𝓞 F)) a b, (CohB.ratAf F n
        (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (𝓞 F) F) k)) a b ∈ Ohat F :=
      fun k a b => (alg_mem_Ohat _).2 ⟨k a b, rfl⟩
    refine ⟨h1 k, fun a b => ?_, fun a b => ⟨_, ?_, by rw [Nat.cast_one]; exact (one_mul _).symm⟩⟩
    · rw [← map_inv, ← map_inv]; exact h1 _ a b
    · refine sub_mem (h1 k a b) ?_
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
