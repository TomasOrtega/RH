import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import GroundTheory.GlobalFields.Adele.Topology
open UpperTheory.V.Lit.Geo NumberField Matrix GlobalTheory.CuspRep Topology Filter

/- English proof (translation)
Introduce `E _ _ a U hU`. Set `O : Set (Af E)` to `GroundTheory.Global.integralFiniteAdeles (𝓞 E) E`. Establish `hOo : IsOpen O` using `GroundTheory.Global.isOpen_integralFiniteAdeles (R := 𝓞 E) (K := E)`. Establish `hOc : IsCompact O` using `GroundTheory.Global.isCompact_integralFiniteAdeles E`. Set `B : Set (Fin a → Af E)` to `Set.univ.pi fun _ => O`.

Establish `hBo : IsOpen B` using `isOpen_set_pi Set.finite_univ fun _ _ => hOo`. Establish `hBc : IsCompact B` using `isCompact_univ_pi fun _ => hOc`. Establish `hB0 : (0 : Fin a → Af E) ∈ B` using `fun _ _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E).zero_mem`. Set `L : AddSubgroup (Fin a → Af E)` to `{ carrier := {x | ∀ u ∈ U, x ᵥ* u.val ∈ B} zero_mem' := fun u _ => by rw [Matrix.zero_vecMul]; exact hB0 add_mem' := fun {x y} hx hy u hu => by`. Rewrite using `[Matrix.add_vecMul]`.

Conclude with `fun i hi => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E).add_mem (hx u hu i hi) (hy u hu i hi)`. Use the proof step `neg_mem' := fun {x} hx u hu => by`. Rewrite using `[Matrix.neg_vecMul]`. Conclude with `fun i hi => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E).neg_mem (hx u hu i hi) }`. Establish `hc : Continuous fun p : (Fin a → Af E) × GL (Fin a) (Af E) => p.1 ᵥ* p.2.val` using `continuous_fst.matrix_vecMul (Units.continuous_val.comp continuous_snd)`.

Establish `hn : (L : Set (Fin a → Af E)) ∈ 𝓝 0`. Use `hU.eventually_forall_of_forall_eventually (x₀ := (0 : Fin a → Af E)) (P := fun x (u : GL (Fin a) (Af E)) => x ᵥ* u.val ∈ B) fun u _ => ?_` and prove the remaining obligations. Use `hc.continuousAt.eventually_mem (hBo.mem_nhds ?_)` and prove the remaining obligations. Simplify `hB0` using `only [Matrix.zero_vecMul]`. Establish `ho : IsOpen (L : Set (Fin a → Af E))` using `L.isOpen_of_mem_nhds hn`.

Use `⟨L, ⟨ho, hBc.of_isClosed_subset (L.isClosed_of_isOpen ho) fun x hx => ?_⟩, fun u hu x hx v hv => ?_⟩` and prove the remaining obligations. Simplify `hx 1 U.one_mem` using `only [Units.val_one, Matrix.vecMul_one]`. Rewrite using `[Matrix.vecMul_vecMul]`. Conclude with `hx (u * v) (U.mul_mem hu hv)`.
-/
theorem UpperTheory.unitaryGroup_lieAlgebra_eq_skewHermitian :
    LatEx := by
  intro E _ _ a U hU
  let O : Set (Af E) := GroundTheory.Global.integralFiniteAdeles (𝓞 E) E
  have hOo : IsOpen O := GroundTheory.Global.isOpen_integralFiniteAdeles (R := 𝓞 E) (K := E)
  have hOc : IsCompact O := GroundTheory.Global.isCompact_integralFiniteAdeles E
  let B : Set (Fin a → Af E) := Set.univ.pi fun _ => O
  have hBo : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => hOo
  have hBc : IsCompact B := isCompact_univ_pi fun _ => hOc
  have hB0 : (0 : Fin a → Af E) ∈ B := fun _ _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E).zero_mem
  let L : AddSubgroup (Fin a → Af E) :=
    { carrier := {x | ∀ u ∈ U, x ᵥ* u.val ∈ B}
      zero_mem' := fun u _ => by rw [Matrix.zero_vecMul]; exact hB0
      add_mem' := fun {x y} hx hy u hu => by
        rw [Matrix.add_vecMul]
        exact fun i hi => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E).add_mem (hx u hu i hi) (hy u hu i hi)
      neg_mem' := fun {x} hx u hu => by
        rw [Matrix.neg_vecMul]
        exact fun i hi => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E).neg_mem (hx u hu i hi) }
  have hc : Continuous fun p : (Fin a → Af E) × GL (Fin a) (Af E) => p.1 ᵥ* p.2.val :=
    continuous_fst.matrix_vecMul (Units.continuous_val.comp continuous_snd)
  have hn : (L : Set (Fin a → Af E)) ∈ 𝓝 0 := by
    refine hU.eventually_forall_of_forall_eventually (x₀ := (0 : Fin a → Af E))
      (P := fun x (u : GL (Fin a) (Af E)) => x ᵥ* u.val ∈ B) fun u _ => ?_
    refine hc.continuousAt.eventually_mem (hBo.mem_nhds ?_)
    simpa only [Matrix.zero_vecMul] using hB0
  have ho : IsOpen (L : Set (Fin a → Af E)) := L.isOpen_of_mem_nhds hn
  refine ⟨L, ⟨ho, hBc.of_isClosed_subset (L.isClosed_of_isOpen ho) fun x hx => ?_⟩, fun u hu x hx v hv => ?_⟩
  · simpa only [Units.val_one, Matrix.vecMul_one] using hx 1 U.one_mem
  · rw [Matrix.vecMul_vecMul]
    exact hx (u * v) (U.mul_mem hu hv)
