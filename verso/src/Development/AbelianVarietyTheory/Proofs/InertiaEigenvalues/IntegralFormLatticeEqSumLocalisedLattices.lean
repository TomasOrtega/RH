import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralizedEigenPartProjectorMemHeckeAlgebraStatement

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.LatSplit

/- English proof (translation)
Use `haveI : Finite ι := hb.1.finite`. Use `haveI := Fintype.ofFinite ι`. Set `B : Module.Basis ι ℂ M` to `Module.Basis.mk hb.1 hb.2.ge`. Establish `hB : ∀ i, B i = j (b i)` using `fun i => by simp [B]`. Establish `key : ∀ l : V →ₗ[L] L, ∃ l' : M →ₗ[ℂ] ℂ, ∀ x, l' (j x) = σ (l x)` using `fun l => by`.

Use `⟨B.constr ℂ fun i => σ (l (b i)), fun x => ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← b.sum_repr x]`. Use `conv_rhs => rw [← b.sum_repr x]`. Simplify using `only [map_sum, LinearMap.map_smulₛₗ, ← hB, Module.Basis.constr_basis, smul_eq_mul, map_mul, RingHom.id_apply]`. Establish `hinj : Function.Injective j` using `fun x y hxy => by`.

Use `b.ext_elem fun i => σ.injective ?_` and prove the remaining obligations. Take `⟨l', hl'⟩` from `key (b.coord i)`. Establish `h1` using `hl' x`. Rewrite `h1` using `[hxy, hl' y]`. Conclude with `h1.symm`.

Use `⟨T.finite_toSet.preimage hinj.injOn, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨l, hl0, hl⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Take `⟨l', hl'⟩` from `key l`. Establish `h1 : l' = 0`.

Rewrite using `[← LinearMap.ker_eq_top, eq_top_iff, ← hT, Submodule.span_le]`. Introduce `y hy`. Take `⟨x, rfl⟩` from `hsub y hy`. Establish `hx : l x = 0` using `hl (Submodule.subset_span hy)`. Use `show l' (j x) = 0`.

Rewrite using `[hl', hx, map_zero]`. Use `hl0 (LinearMap.ext fun x => σ.injective ?_)` and prove the remaining obligations. Rewrite using `[← hl', h1]`. Simplify using the standard rewrite rules.
-/
theorem form_gen_span {L V M ι : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] {σ : L →+* ℂ} (j : V →ₛₗ[σ] M) (b : Module.Basis ι L V)
    (hb : LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤)
    (T : Finset M) (hT : Submodule.span ℂ (T : Set M) = ⊤) (hsub : ∀ x ∈ T, x ∈ Set.range j) :
    {x | j x ∈ T}.Finite ∧ Submodule.span L {x | j x ∈ T} = ⊤ := by
  haveI : Finite ι := hb.1.finite
  haveI := Fintype.ofFinite ι
  let B : Module.Basis ι ℂ M := Module.Basis.mk hb.1 hb.2.ge
  have hB : ∀ i, B i = j (b i) := fun i => by simp [B]
  have key : ∀ l : V →ₗ[L] L, ∃ l' : M →ₗ[ℂ] ℂ, ∀ x, l' (j x) = σ (l x) := fun l => by
    refine ⟨B.constr ℂ fun i => σ (l (b i)), fun x => ?_⟩
    conv_lhs => rw [← b.sum_repr x]
    conv_rhs => rw [← b.sum_repr x]
    simp only [map_sum, LinearMap.map_smulₛₗ, ← hB, Module.Basis.constr_basis, smul_eq_mul, map_mul, RingHom.id_apply]
  have hinj : Function.Injective j := fun x y hxy => by
    refine b.ext_elem fun i => σ.injective ?_
    obtain ⟨l', hl'⟩ := key (b.coord i)
    have h1 := hl' x
    rw [hxy, hl' y] at h1
    exact h1.symm
  refine ⟨T.finite_toSet.preimage hinj.injOn, ?_⟩
  by_contra hne
  obtain ⟨l, hl0, hl⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨l', hl'⟩ := key l
  have h1 : l' = 0 := by
    rw [← LinearMap.ker_eq_top, eq_top_iff, ← hT, Submodule.span_le]
    intro y hy
    obtain ⟨x, rfl⟩ := hsub y hy
    have hx : l x = 0 := hl (Submodule.subset_span hy)
    show l' (j x) = 0
    rw [hl', hx, map_zero]
  refine hl0 (LinearMap.ext fun x => σ.injective ?_)
  rw [← hl', h1]
  simp

variable {D : D7} {M : MtFam D}

/- English proof (translation)
The claim follows from `form_gen_span (D.what₂.jMt _ j) (Module.Free.chooseBasis _ _) (D.what₂.jMt_basis _ j _) _ (D.what₂.MtLat _ j).span_top (D.what₂.MtLat_sub _ j)`.
-/
theorem genSet_props (j : ℕ) (w : D.what₂.places.Pl) :
    (genSet D (D.what₂.muTw w) j).Finite ∧ Submodule.span D.what₂.LL (genSet D (D.what₂.muTw w) j) = ⊤ :=
  form_gen_span (D.what₂.jMt _ j) (Module.Free.chooseBasis _ _) (D.what₂.jMt_basis _ j _) _
    (D.what₂.MtLat _ j).span_top (D.what₂.MtLat_sub _ j)

/- English proof (translation)
The claim follows from `Submodule.fg_span ((genSet_props (D := D) j w).1.image _)`.
-/
theorem latLoc_fg (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) : (latLoc B j w).FG :=
  Submodule.fg_span ((genSet_props (D := D) j w).1.image _)

/- English proof (translation)
Rewrite using `[latLoc, Submodule.span_span_of_tower]`. Establish `hG` using `(genSet_props (D := D) j w).2`. Establish `key : ∀ x ∈ Submodule.span D.what₂.LL (genSet D (D.what₂.muTw w) j), B.iV j w x ∈ Submodule.span (FractionRing (B.Oc j w)) (B.iV j w '' genSet D (D.what₂.muTw w) j)`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul c y _ hy => rw [LinearMap.map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ hy`. Set `b` to `Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)`. Rewrite using `[eq_top_iff, ← (B.iV_basis j w b).2, Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`.

Conclude with `key _ (hG ▸ Submodule.mem_top)`.
-/
theorem latLoc_span (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) :
    Submodule.span (FractionRing (B.Oc j w)) (latLoc B j w : Set (B.V j w)) = ⊤ := by
  rw [latLoc, Submodule.span_span_of_tower]
  have hG := (genSet_props (D := D) j w).2
  have key : ∀ x ∈ Submodule.span D.what₂.LL (genSet D (D.what₂.muTw w) j),
      B.iV j w x ∈ Submodule.span (FractionRing (B.Oc j w)) (B.iV j w '' genSet D (D.what₂.muTw w) j) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  rw [eq_top_iff, ← (B.iV_basis j w b).2, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact key _ (hG ▸ Submodule.mem_top)

/- English proof (translation)
Introduce `t ht`. Proceed by induction on `ht using Algebra.adjoin_induction with`. Consider the case `mem f hf`. Take `⟨v, k, hvk, rfl⟩` from `hf`. Conclude with `hl v k hvk`.

Consider the case `algebraMap r`. Introduce `x hx`. Rewrite using `[Module.algebraMap_end_apply]`. Conclude with `(latLoc B j w).smul_mem r hx`. Consider the case `add f g _ _ hf hg => intro x hx`.

Conclude with `Submodule.add_mem _ (hf x hx) (hg x hx)`. Consider the case `mul f g _ _ hf hg => intro x hx`. Conclude with `hf _ (hg x hx)`.
-/
theorem alg_stable (B : NLocBase D M) {j : ℕ} {w : D.what₂.places.Pl} (hl : LatStable B j w) :
    ∀ t ∈ heckeAlg B j w, ∀ x ∈ latLoc B j w, t x ∈ latLoc B j w := by
  intro t ht
  induction ht using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨v, k, hvk, rfl⟩ := hf
    exact hl v k hvk
  | algebraMap r =>
    intro x hx
    rw [Module.algebraMap_end_apply]
    exact (latLoc B j w).smul_mem r hx
  | add f g _ _ hf hg => intro x hx; exact Submodule.add_mem _ (hf x hx) (hg x hx)
  | mul f g _ _ hf hg => intro x hx; exact hf _ (hg x hx)

end GlobalTheory.LatSplit

namespace GlobalTheory.LatSplit

variable {D : D7} {M : MtFam D}

/- English proof (translation)
Establish `hy : y ∈ P ⊔ Q` using `hc.sup_eq_top ▸ Submodule.mem_top`. Take `⟨p, hp, q, hq, rfl⟩` from `Submodule.mem_sup.1 hy`. Rewrite using `[map_add, hP p hp, hQ q hq, add_zero, add_sub_cancel_left]`. Conclude with `⟨hp, hq⟩`.
-/
theorem proj_facts {K V : Type} [Field K] [AddCommGroup V] [Module K V] {P Q : Submodule K V} (hc : IsCompl P Q)
    (t : Module.End K V) (hP : ∀ x ∈ P, t x = x) (hQ : ∀ x ∈ Q, t x = 0) (y : V) : t y ∈ P ∧ y - t y ∈ Q := by
  have hy : y ∈ P ⊔ Q := hc.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add, hP p hp, hQ q hq, add_zero, add_sub_cancel_left]
  exact ⟨hp, hq⟩

/- English proof (translation)
The claim follows from `iSup₂_le fun ψ hψ => le_iSup₂_of_le (f := fun ψ (_ : NCov.cls ψ ≠ J) => NCov.W T (NCov.pt ψ)) ψ (by rw [hψ]; exact h) le_rfl`.
-/
theorem part_le_off {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] [IsLocalRing O] (T : Subalgebra O (Module.End K V)) {I J : Ideal T} (h : I ≠ J) :
    NCov.part T I ≤ NCov.off T J :=
  iSup₂_le fun ψ hψ => le_iSup₂_of_le (f := fun ψ (_ : NCov.cls ψ ≠ J) => NCov.W T (NCov.pt ψ)) ψ
    (by rw [hψ]; exact h) le_rfl

/- English proof (translation)
Take `⟨hfd, -⟩` from `finrank_V T.B j w`. Use `haveI := hfd`. Take `⟨hS, hsplit, hint⟩` from `gens_hypsTw T.B hstd h1 h2 (Or.inl hw)`. Conclude with `GlobalTheory.T.generalizedEigenPartProjector_mem_heckeAlgebra (T.B.Oc j w) (FractionRing (T.B.Oc j w)) (T.B.V j w) (heckeGens T.B j w) hS hsplit hint (latLoc T.B j w) (latLoc_fg T.B j w) (latLoc_span T.B j w) (fun a ha x hx => alg_stable T.B hl a (Algebra.subset_adjoin ha) x hx) …`.
-/
theorem exists_proj (T : NormalizedLocalCompatibility D M) (hstd : HeckeStdTw T.B) {j : ℕ} {w : D.what₂.places.Pl} (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (hw : D.what₂.muAt w ≠ D.what₂.mu0) (hl : LatStable T.B j w) (I : Ideal (heckeAlg T.B j w)) :
    ∃ t ∈ heckeAlg T.B j w, (∀ x ∈ NCov.part (heckeAlg T.B j w) I, t x = x) ∧
      ∀ x ∈ NCov.off (heckeAlg T.B j w) I, t x = 0 := by
  obtain ⟨hfd, -⟩ := finrank_V T.B j w
  haveI := hfd
  obtain ⟨hS, hsplit, hint⟩ := gens_hypsTw T.B hstd h1 h2 (Or.inl hw)
  exact GlobalTheory.T.generalizedEigenPartProjector_mem_heckeAlgebra (T.B.Oc j w) (FractionRing (T.B.Oc j w)) (T.B.V j w) (heckeGens T.B j w) hS hsplit hint
    (latLoc T.B j w) (latLoc_fg T.B j w) (latLoc_span T.B j w)
    (fun a ha x hx => alg_stable T.B hl a (Algebra.subset_adjoin ha) x hx) I

/- English proof (translation)
Introduce `D M T j w h1 h2 hw hstd hl y`. Take `⟨hfd, -⟩` from `finrank_V T.B j w`. Use `haveI := hfd`. Take `⟨hS, hsplit, hint⟩` from `gens_hypsTw T.B hstd h1 h2 (Or.inl hw)`. Establish `hinj` using `IsFractionRing.injective (T.B.Oc j w) (FractionRing (T.B.Oc j w))`.

Use `choose tp htp hpart hoff using exists_proj T hstd h1 h2 hw hl`. Establish `hc` using `fun I => NCov.isCompl_part_off hinj hS hsplit hint I`. Establish `eL : latC T.B j w = latLoc T.B j w` using `rfl`. Establish `hlp : ∀ I x, x ∈ NCov.latPart (heckeAlg T.B j w) (latC T.B j w) I → x ∈ latLoc T.B j w`. Introduce `I x hx`.

Take `⟨hxP, hxL⟩` from `Submodule.mem_inf.1 hx`. Take `⟨l, hlL, q, hq, rfl⟩` from `Submodule.mem_sup.1 hxL`. Establish `e : tp I (l + q) = l + q` using `hpart I _ hxP`. Rewrite `e` using `[map_add, hoff I q hq, add_zero]`. Rewrite using `[← e]`.

Conclude with `alg_stable T.B hl _ (htp I) l hlL`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `ex : ∀ i (h : i ∈ D.nd.locs j w), ∃ z, z ∈ D.nd.MtIn i ∧ T.Psi j w i h z = tp (T.mx j w i) y`. Introduce `i h`.

Use `haveI := RingHomInvPair.of_ringEquiv (T.phO j w i h)`. Establish `hm : tp (T.mx j w i) y ∈ NCov.latPart (heckeAlg T.B j w) (latC T.B j w) (T.mx j w i)`. Use `Submodule.mem_inf.2 ⟨(proj_facts (hc _) _ (hpart _) (hoff _) y).1, ?_⟩` and prove the remaining obligations. Conclude with `Submodule.mem_sup_left (alg_stable T.B hl _ (htp _) y hy)`. Rewrite `hm` using `[← map_psiO_MtIn T hstd h]`.

Take `⟨z, hz, e⟩` from `Submodule.mem_map.1 hm`. Conclude with `⟨z, hz, e⟩`. Use `⟨fun i => if h : i ∈ D.nd.locs j w then (ex i h).choose else 0, fun i => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : i ∈ D.nd.locs j w`. Simplify using `only`.

Rewrite using `[dif_pos h]`. Conclude with `(ex i h).choose_spec.1`. Simplify using `only`. Rewrite using `[dif_neg h]`. Conclude with `Submodule.zero_mem _`.

Establish `hsum : ∑ i ∈ (D.nd.locs j w).attach, T.Psi j w i.1 i.2 (if h : i.1 ∈ D.nd.locs j w then (ex i.1 h).choose else 0) = ∑ i ∈ (D.nd.locs j w).attach, tp (T.mx j w i.1) y`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[dif_pos i.2]`. Conclude with `(ex i.1 i.2).choose_spec.2`. Rewrite using `[hsum, ← sub_eq_zero]`.

Use `NCov.eq_zero_of_forall_mem_off hinj hS hsplit hint ((D.nd.locs j w).image (T.mx j w)) (fun I hI => ?_) ?_` and prove the remaining obligations. Take `⟨i, hi, rfl⟩` from `T.mx_all j w h1 h2 hw I hI`. Conclude with `Finset.mem_image_of_mem _ hi`. Introduce `I hI`. Take `⟨i0, hi0, rfl⟩` from `Finset.mem_image.1 hI`.

Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_attach _ ⟨i0, hi0⟩), sub_add_eq_sub_sub]`. Use `Submodule.sub_mem _ (proj_facts (hc _) _ (hpart _) (hoff _) y).2 (Submodule.sum_mem _ fun i hi => ?_)` and prove the remaining obligations. Establish `hne : T.mx j w i.1 ≠ T.mx j w i0`. Introduce `e`. Use `T.mx_inj j w i.2 hi0 e` as an intermediate fact.

Conclude with `(Finset.mem_erase.1 hi).1 (Subtype.ext this)`. Conclude with `part_le_off _ hne (proj_facts (hc _) _ (hpart _) (hoff _) y).1`. Introduce and unpack `⟨z, hz, rfl⟩`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Use `haveI := RingHomInvPair.of_ringEquiv (T.phO j w i.1 i.2)`.

Use `hlp (T.mx j w i.1) _ ?_` and prove the remaining obligations. Rewrite using `[← map_psiO_MtIn T hstd i.2]`. Conclude with `Submodule.mem_map_of_mem (hz i.1)`.
-/
theorem main : ∀ (D : D7) (M : MtFam D) (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl), 1 ≤ j → j ≤ D.R.m →
    D.what₂.muAt w ≠ D.what₂.mu0 → HeckeStdTw T.B → LatStable T.B j w → ∀ y : T.B.V j w,
    y ∈ latLoc T.B j w ↔ ∃ z : ∀ i : D.nd.Loc, TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i),
      (∀ i, z i ∈ D.nd.MtIn i) ∧ y = ∑ i ∈ (D.nd.locs j w).attach, T.Psi j w i.1 i.2 (z i.1) := by
  classical
  intro D M T j w h1 h2 hw hstd hl y
  obtain ⟨hfd, -⟩ := finrank_V T.B j w
  haveI := hfd
  obtain ⟨hS, hsplit, hint⟩ := gens_hypsTw T.B hstd h1 h2 (Or.inl hw)
  have hinj := IsFractionRing.injective (T.B.Oc j w) (FractionRing (T.B.Oc j w))
  choose tp htp hpart hoff using exists_proj T hstd h1 h2 hw hl
  have hc := fun I => NCov.isCompl_part_off hinj hS hsplit hint I
  have eL : latC T.B j w = latLoc T.B j w := rfl

  have hlp : ∀ I x, x ∈ NCov.latPart (heckeAlg T.B j w) (latC T.B j w) I → x ∈ latLoc T.B j w := by
    intro I x hx
    obtain ⟨hxP, hxL⟩ := Submodule.mem_inf.1 hx
    obtain ⟨l, hlL, q, hq, rfl⟩ := Submodule.mem_sup.1 hxL
    have e : tp I (l + q) = l + q := hpart I _ hxP
    rw [map_add, hoff I q hq, add_zero] at e
    rw [← e]
    exact alg_stable T.B hl _ (htp I) l hlL
  constructor
  · intro hy

    have ex : ∀ i (h : i ∈ D.nd.locs j w), ∃ z, z ∈ D.nd.MtIn i ∧ T.Psi j w i h z = tp (T.mx j w i) y := by
      intro i h
      haveI := RingHomInvPair.of_ringEquiv (T.phO j w i h)
      have hm : tp (T.mx j w i) y ∈ NCov.latPart (heckeAlg T.B j w) (latC T.B j w) (T.mx j w i) := by
        refine Submodule.mem_inf.2 ⟨(proj_facts (hc _) _ (hpart _) (hoff _) y).1, ?_⟩
        exact Submodule.mem_sup_left (alg_stable T.B hl _ (htp _) y hy)
      rw [← map_psiO_MtIn T hstd h] at hm
      obtain ⟨z, hz, e⟩ := Submodule.mem_map.1 hm
      exact ⟨z, hz, e⟩
    refine ⟨fun i => if h : i ∈ D.nd.locs j w then (ex i h).choose else 0, fun i => ?_, ?_⟩
    · by_cases h : i ∈ D.nd.locs j w
      · dsimp only; rw [dif_pos h]; exact (ex i h).choose_spec.1
      · dsimp only; rw [dif_neg h]; exact Submodule.zero_mem _
    · have hsum : ∑ i ∈ (D.nd.locs j w).attach,
          T.Psi j w i.1 i.2 (if h : i.1 ∈ D.nd.locs j w then (ex i.1 h).choose else 0) =
          ∑ i ∈ (D.nd.locs j w).attach, tp (T.mx j w i.1) y := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [dif_pos i.2]
        exact (ex i.1 i.2).choose_spec.2
      rw [hsum, ← sub_eq_zero]
      refine NCov.eq_zero_of_forall_mem_off hinj hS hsplit hint ((D.nd.locs j w).image (T.mx j w))
        (fun I hI => ?_) ?_
      · obtain ⟨i, hi, rfl⟩ := T.mx_all j w h1 h2 hw I hI
        exact Finset.mem_image_of_mem _ hi
      · intro I hI
        obtain ⟨i0, hi0, rfl⟩ := Finset.mem_image.1 hI
        rw [← Finset.add_sum_erase _ _ (Finset.mem_attach _ ⟨i0, hi0⟩), sub_add_eq_sub_sub]
        refine Submodule.sub_mem _ (proj_facts (hc _) _ (hpart _) (hoff _) y).2 (Submodule.sum_mem _ fun i hi => ?_)
        have hne : T.mx j w i.1 ≠ T.mx j w i0 := by
          intro e
          have := T.mx_inj j w i.2 hi0 e
          exact (Finset.mem_erase.1 hi).1 (Subtype.ext this)
        exact part_le_off _ hne (proj_facts (hc _) _ (hpart _) (hoff _) y).1
  · rintro ⟨z, hz, rfl⟩
    refine Submodule.sum_mem _ fun i _ => ?_
    haveI := RingHomInvPair.of_ringEquiv (T.phO j w i.1 i.2)
    refine hlp (T.mx j w i.1) _ ?_
    rw [← map_psiO_MtIn T hstd i.2]
    exact Submodule.mem_map_of_mem (hz i.1)

end GlobalTheory.LatSplit
