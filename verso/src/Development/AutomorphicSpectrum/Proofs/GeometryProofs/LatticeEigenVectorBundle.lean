import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelatedPairsOrbitalTermEq
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjSumSumEmbeddingsEqTrace
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.EigSplit

open Module NumberField

section Local

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Establish `hee : ∀ v, e (e v) = e v` using `fun v => LinearMap.congr_fun he v`. Establish `hbR : LinearIndependent R b` using `hb.restrict_scalars (by`. Introduce `x y hxy`. Simplify `hxy)` using `[Subring.smul_def]`. Set `bM : Basis (Fin g) R M` to `by`.

Rewrite using `[hM]`. Conclude with `Basis.span hbR`. Use `haveI : Module.Free R M := Module.Free.of_basis bM`. Use `haveI : Module.Finite R M := Module.Finite.of_basis bM`. Set `P : M →ₗ[R] M` to `LinearMap.restrict (e.restrictScalars R) hMe`.

Establish `hPP : ∀ m, P (P m) = P m` using `fun m => Subtype.ext (hee m)`. Set `Q : M →ₗ[R] M` to `LinearMap.id - P`. Establish `hQQ : ∀ m, Q (Q m) = Q m` using `fun m => by simp [Q, hPP]`. Establish `key : ∀ (A : M →ₗ[R] M), (∀ m, A (A m) = A m) → Module.Free R (LinearMap.range A) ∧ Module.Finite R (LinearMap.range A)`. Introduce `A hA`.

Set `π : M →ₗ[R] LinearMap.range A` to `A.rangeRestrict`. Set `inc : LinearMap.range A →ₗ[R] M` to `(LinearMap.range A).subtype`. Establish `hπι : π ∘ₗ inc = LinearMap.id`. Use extensionality with `⟨_, m, rfl⟩`. Simplify using `[π, inc, hA]`.

Use `haveI : Module.Finite R (LinearMap.range A) := Module.Finite.range A`. Use `haveI : Module.Projective R (LinearMap.range A) := Module.Projective.of_split inc π hπι`. Conclude with `⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩`. Take `⟨h1, h2⟩` from `key P hPP`. Take `⟨h3, h4⟩` from `key Q hQQ`.

Set `B` to `Module.finBasis R (LinearMap.range P)`. Set `B'` to `Module.finBasis R (LinearMap.range Q)`. Set `f : Fin (finrank R (LinearMap.range P)) → E` to `fun i => ((B i : M) : E)`. Set `f' : Fin (finrank R (LinearMap.range Q)) → E` to `fun i => ((B' i : M) : E)`. Establish `hfe : ∀ i, e (f i) = f i`.

Introduce `i`. Take `⟨m, hm⟩` from `(B i).2`. Establish `: f i = e m` using `by simp only [f]; rw [← hm]; rfl`. Rewrite using `[this, hee]`. Establish `hfe' : ∀ i, e (f' i) = 0`.

Introduce `i`. Take `⟨m, hm⟩` from `(B' i).2`. Establish `: f' i = (m : E) - e m` using `by simp only [f']; rw [← hm]; rfl`. Rewrite using `[this, map_sub, hee, sub_self]`. Establish `hinl : ∀ n : LinearMap.range P, ((n : M) : E) ∈ Submodule.span R (Set.range (Sum.elim f f'))`.

Introduce `n`. Establish `hmem` using `Submodule.mem_map_of_mem (f := M.subtype ∘ₗ (LinearMap.range P).subtype) (B.mem_span n)`. Rewrite `hmem` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl i, rfl⟩) hmem`. Establish `hinr : ∀ n : LinearMap.range Q, ((n : M) : E) ∈ Submodule.span R (Set.range (Sum.elim f f'))`.

Introduce `n`. Establish `hmem` using `Submodule.mem_map_of_mem (f := M.subtype ∘ₗ (LinearMap.range Q).subtype) (B'.mem_span n)`. Rewrite `hmem` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Sum.inr i, rfl⟩) hmem`. Establish `hspanR : Submodule.span R (Set.range (Sum.elim f f')) = M`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i | i, rfl⟩`. Conclude with `(B i : M).2`. Conclude with `(B' i : M).2`.

Introduce `v hv`. Establish `h` using `add_mem (hinl ⟨P ⟨v, hv⟩, LinearMap.mem_range_self _ _⟩) (hinr ⟨Q ⟨v, hv⟩, LinearMap.mem_range_self _ _⟩)`. Simplify `h` using `[Q]`. Establish `hspanΩ : Submodule.span Ω (Set.range (Sum.elim f f')) = ⊤`. Rewrite using `[eq_top_iff, ← hspan, Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Establish `h1 : b i ∈ M` using `hM ▸ Submodule.subset_span ⟨i, rfl⟩`. Rewrite `h1` using `[← hspanR]`. Conclude with `Submodule.span_subset_span R Ω _ h1`. Set `eqv : M ≃ₗ[R] (LinearMap.range P × LinearMap.range Q)` to `LinearEquiv.ofLinear (P.rangeRestrict.prod Q.rangeRestrict) ((LinearMap.range P).subtype.coprod (LinearMap.range Q).subtype) (by`.

Establish `hPQ : ∀ m, P (Q m) = 0` using `fun m => by simp [Q, hPP]`. Establish `hQP : ∀ m, Q (P m) = 0` using `fun m => by simp [Q, hPP]`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce and unpack `⟨⟨_, m, rfl⟩, ⟨_, m', rfl⟩⟩`. Apply the tactic sequence `apply Prod.ext <;> apply Subtype.ext <;> simp [hPP, hQQ, hPQ, hQP])`.

Use the proof step `(by ext m; simp [Q])`. Establish `hcard : finrank R (LinearMap.range P) + finrank R (LinearMap.range Q) = g`. Rewrite using `[← Module.finrank_prod, ← LinearEquiv.finrank_eq eqv, Module.finrank_eq_card_basis bM, Fintype.card_fin]`. Use `haveI : FiniteDimensional Ω E := Module.Finite.of_basis (Basis.mk hb hspan.ge)`. Establish `hfin : finrank Ω E = g`.

Use `finrank_span_eq_card hb` as an intermediate fact. Rewrite `this` using `[hspan, finrank_top, Fintype.card_fin]`. Then use the resulting hypothesis. Use `⟨_, _, f, f', ?_, hspanΩ, hspanR, hfe, hfe'⟩` and prove the remaining obligations. Apply `linearIndependent_of_top_le_span_of_card_eq_finrank hspanΩ.ge` to reduce the goal to its premises. Rewrite using `[Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hcard, hfin]`.
-/
theorem exists_frame_of_proj (R : Subring Ω) [IsLocalRing R] (M : Submodule R E) {g : ℕ} (b : Fin g → E)
    (hb : LinearIndependent Ω b) (hspan : Submodule.span Ω (Set.range b) = ⊤)
    (hM : M = Submodule.span R (Set.range b)) (e : E →ₗ[Ω] E) (he : e ∘ₗ e = e) (hMe : ∀ v ∈ M, e v ∈ M) :
    ∃ (r r' : ℕ) (f : Fin r → E) (f' : Fin r' → E),
      LinearIndependent Ω (Sum.elim f f') ∧ Submodule.span Ω (Set.range (Sum.elim f f')) = ⊤ ∧
      Submodule.span R (Set.range (Sum.elim f f')) = M ∧ (∀ i, e (f i) = f i) ∧ (∀ i, e (f' i) = 0) := by
  classical
  have hee : ∀ v, e (e v) = e v := fun v => LinearMap.congr_fun he v
  have hbR : LinearIndependent R b := hb.restrict_scalars (by
    intro x y hxy
    simpa [Subring.smul_def] using hxy)
  let bM : Basis (Fin g) R M := by
    rw [hM]; exact Basis.span hbR
  haveI : Module.Free R M := Module.Free.of_basis bM
  haveI : Module.Finite R M := Module.Finite.of_basis bM

  let P : M →ₗ[R] M := LinearMap.restrict (e.restrictScalars R) hMe
  have hPP : ∀ m, P (P m) = P m := fun m => Subtype.ext (hee m)
  let Q : M →ₗ[R] M := LinearMap.id - P
  have hQQ : ∀ m, Q (Q m) = Q m := fun m => by simp [Q, hPP]
  have key : ∀ (A : M →ₗ[R] M), (∀ m, A (A m) = A m) →
      Module.Free R (LinearMap.range A) ∧ Module.Finite R (LinearMap.range A) := by
    intro A hA
    let π : M →ₗ[R] LinearMap.range A := A.rangeRestrict
    let inc : LinearMap.range A →ₗ[R] M := (LinearMap.range A).subtype
    have hπι : π ∘ₗ inc = LinearMap.id := by
      ext ⟨_, m, rfl⟩
      simp [π, inc, hA]
    haveI : Module.Finite R (LinearMap.range A) := Module.Finite.range A
    haveI : Module.Projective R (LinearMap.range A) := Module.Projective.of_split inc π hπι
    exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩
  obtain ⟨h1, h2⟩ := key P hPP
  obtain ⟨h3, h4⟩ := key Q hQQ
  let B := Module.finBasis R (LinearMap.range P)
  let B' := Module.finBasis R (LinearMap.range Q)
  let f : Fin (finrank R (LinearMap.range P)) → E := fun i => ((B i : M) : E)
  let f' : Fin (finrank R (LinearMap.range Q)) → E := fun i => ((B' i : M) : E)
  have hfe : ∀ i, e (f i) = f i := by
    intro i
    obtain ⟨m, hm⟩ := (B i).2
    have : f i = e m := by simp only [f]; rw [← hm]; rfl
    rw [this, hee]
  have hfe' : ∀ i, e (f' i) = 0 := by
    intro i
    obtain ⟨m, hm⟩ := (B' i).2
    have : f' i = (m : E) - e m := by simp only [f']; rw [← hm]; rfl
    rw [this, map_sub, hee, sub_self]
  have hinl : ∀ n : LinearMap.range P, ((n : M) : E) ∈ Submodule.span R (Set.range (Sum.elim f f')) := by
    intro n
    have hmem := Submodule.mem_map_of_mem (f := M.subtype ∘ₗ (LinearMap.range P).subtype) (B.mem_span n)
    rw [Submodule.map_span, ← Set.range_comp] at hmem
    exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl i, rfl⟩) hmem
  have hinr : ∀ n : LinearMap.range Q, ((n : M) : E) ∈ Submodule.span R (Set.range (Sum.elim f f')) := by
    intro n
    have hmem := Submodule.mem_map_of_mem (f := M.subtype ∘ₗ (LinearMap.range Q).subtype) (B'.mem_span n)
    rw [Submodule.map_span, ← Set.range_comp] at hmem
    exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Sum.inr i, rfl⟩) hmem
  have hspanR : Submodule.span R (Set.range (Sum.elim f f')) = M := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i | i, rfl⟩
      · exact (B i : M).2
      · exact (B' i : M).2
    · intro v hv
      have h := add_mem (hinl ⟨P ⟨v, hv⟩, LinearMap.mem_range_self _ _⟩)
        (hinr ⟨Q ⟨v, hv⟩, LinearMap.mem_range_self _ _⟩)
      simpa [Q] using h
  have hspanΩ : Submodule.span Ω (Set.range (Sum.elim f f')) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : b i ∈ M := hM ▸ Submodule.subset_span ⟨i, rfl⟩
    rw [← hspanR] at h1
    exact Submodule.span_subset_span R Ω _ h1
  let eqv : M ≃ₗ[R] (LinearMap.range P × LinearMap.range Q) := LinearEquiv.ofLinear
    (P.rangeRestrict.prod Q.rangeRestrict)
    ((LinearMap.range P).subtype.coprod (LinearMap.range Q).subtype)
    (by
      have hPQ : ∀ m, P (Q m) = 0 := fun m => by simp [Q, hPP]
      have hQP : ∀ m, Q (P m) = 0 := fun m => by simp [Q, hPP]
      apply LinearMap.ext
      rintro ⟨⟨_, m, rfl⟩, ⟨_, m', rfl⟩⟩
      apply Prod.ext <;> apply Subtype.ext <;> simp [hPP, hQQ, hPQ, hQP])
    (by ext m; simp [Q])
  have hcard : finrank R (LinearMap.range P) + finrank R (LinearMap.range Q) = g := by
    rw [← Module.finrank_prod, ← LinearEquiv.finrank_eq eqv, Module.finrank_eq_card_basis bM, Fintype.card_fin]
  haveI : FiniteDimensional Ω E := Module.Finite.of_basis (Basis.mk hb hspan.ge)
  have hfin : finrank Ω E = g := by
    have := finrank_span_eq_card hb
    rwa [hspan, finrank_top, Fintype.card_fin] at this
  refine ⟨_, _, f, f', ?_, hspanΩ, hspanR, hfe, hfe'⟩
  apply linearIndependent_of_top_le_span_of_card_eq_finrank hspanΩ.ge
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hcard, hfin]

end Local

section Near

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
The claim follows from `IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective`.
-/
theorem isLocalRing_regAt (p : Cpt ξ) : IsLocalRing (regAt ξ p) :=
  IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

/- English proof (translation)
Use `choose U hU hq using fun j => exists_open_mem_regAt ξ p (a j) (ha j)`. Use `⟨⟨⋂ j, (U j : Set X), isOpen_iInter_of_finite fun j => (U j).isOpen⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Set.mem_iInter.2 hU`. Introduce `q hq' j`. Conclude with `hq j q (Set.mem_iInter.1 hq' j)`.
-/
theorem exists_open_forall_mem_regAt (p : Cpt ξ) {κ : Type} [Finite κ] (a : κ → Ω)
    (ha : ∀ j, a j ∈ regAt ξ p) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ j, a j ∈ regAt ξ q := by
  choose U hU hq using fun j => exists_open_mem_regAt ξ p (a j) (ha j)
  refine ⟨⟨⋂ j, (U j : Set X), isOpen_iInter_of_finite fun j => (U j).isOpen⟩, ?_, ?_⟩
  · exact Set.mem_iInter.2 hU
  · intro q hq' j
    exact hq j q (Set.mem_iInter.1 hq' j)

/- English proof (translation)
Use `choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun (regAt ξ p)).1 (h i)`. Take `⟨U, hU, hq⟩` from `exists_open_forall_mem_regAt p (fun ij : J × κ => (c ij.1 ij.2 : Ω)) (fun ij => (c ij.1 ij.2).2)`. Use `⟨U, hU, fun q hqU i => ?_⟩` and prove the remaining obligations. Rewrite using `[← hc i]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Establish `h1 : (c i j) • y j = (⟨(c i j : Ω), hq q hqU (i, j)⟩ : regAt ξ q) • y j` using `rfl`. Rewrite using `[h1]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.
-/
theorem exists_open_mem_span (p : Cpt ξ) {J κ : Type} [Fintype J] [Fintype κ] (x : J → E) (y : κ → E)
    (h : ∀ i, x i ∈ Submodule.span (regAt ξ p) (Set.range y)) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ i,
      x i ∈ Submodule.span (regAt ξ q) (Set.range y) := by
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun (regAt ξ p)).1 (h i)
  obtain ⟨U, hU, hq⟩ := exists_open_forall_mem_regAt p (fun ij : J × κ => (c ij.1 ij.2 : Ω))
    (fun ij => (c ij.1 ij.2).2)
  refine ⟨U, hU, fun q hqU i => ?_⟩
  rw [← hc i]
  refine Submodule.sum_mem _ fun j _ => ?_
  have h1 : (c i j) • y j = (⟨(c i j : Ω), hq q hqU (i, j)⟩ : regAt ξ q) • y j := rfl
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/- English proof (translation)
Establish `h : Submodule.span S (Set.range (Sum.elim f f')) ≤ (Submodule.span S (Set.range f)).comap e`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i | i, rfl⟩`. Simplify using `only [Sum.elim_inl, SetLike.mem_coe, Submodule.mem_comap, hf]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`.

Simplify using `only [Sum.elim_inr, SetLike.mem_coe, Submodule.mem_comap, hf']`. Conclude with `Submodule.zero_mem _`. Conclude with `h hw`.
-/
theorem map_mem_span_elim {S : Type} [Semiring S] [Module S E] (e : E →ₗ[S] E) {J J' : Type}
    (f : J → E) (f' : J' → E) (hf : ∀ i, e (f i) = f i) (hf' : ∀ i, e (f' i) = 0) {w : E}
    (hw : w ∈ Submodule.span S (Set.range (Sum.elim f f'))) : e w ∈ Submodule.span S (Set.range f) := by
  have h : Submodule.span S (Set.range (Sum.elim f f')) ≤ (Submodule.span S (Set.range f)).comap e := by
    rw [Submodule.span_le]
    rintro _ ⟨i | i, rfl⟩
    · simp only [Sum.elim_inl, SetLike.mem_coe, Submodule.mem_comap, hf]
      exact Submodule.subset_span ⟨i, rfl⟩
    · simp only [Sum.elim_inr, SetLike.mem_coe, Submodule.mem_comap, hf']
      exact Submodule.zero_mem _
  exact h hw

/- English proof (translation)
Introduce `p hp`. Take `⟨U, hpU, b, hbs, hfr⟩` from `hVB p hp`. Take `⟨hbi, hbp⟩` from `hfr p hp hpU`. Use `haveI := isLocalRing_regAt p`. Take `⟨r, r', f, f', hli, hsp, hsR, hfe, hfe'⟩` from `exists_frame_of_proj (regAt ξ p) (L p) b hbi hbs hbp e he (hs p hp)`.

Establish `hee : ∀ v, e (e v) = e v` using `fun v => LinearMap.congr_fun he v`. Establish `hfli : LinearIndependent Ω f`. Simplify using `using hli.comp _ Sum.inl_injective`. Establish `hV : Submodule.span Ω (Set.range f) = LinearMap.range e`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨f i, hfe i⟩`. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `map_mem_span_elim e f f' hfe hfe' (hsp ▸ Submodule.mem_top)`.

Establish `hr : r = finrank Ω (LinearMap.range e)`. Use `finrank_span_eq_card hfli` as an intermediate fact. Rewrite `this` using `[hV, Fintype.card_fin]`. Conclude with `this.symm`. Substitute `hr` using the available equality.

Take `⟨U₁, h₁, k₁⟩` from `exists_open_mem_span p (Sum.elim f f') b (fun i => by`. Rewrite using `[← hbp, ← hsR]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩)`. Take `⟨U₂, h₂, k₂⟩` from `exists_open_mem_span p b (Sum.elim f f') (fun i => by`. Rewrite using `[hsR, hbp]`.

Conclude with `Submodule.subset_span ⟨i, rfl⟩)`. Use `⟨U ⊓ U₁ ⊓ U₂, ⟨⟨hpU, h₁⟩, h₂⟩, f, hV, fun q hq hqU => ⟨hfli, ?_⟩⟩` and prove the remaining obligations. Take `⟨⟨hqU0, hqU1⟩, hqU2⟩` from `hqU`. Establish `hLq : L q = Submodule.span (regAt ξ q) (Set.range b)` using `(hfr q hq hqU0).2`. Establish `hspq : Submodule.span (regAt ξ q) (Set.range (Sum.elim f f')) = L q`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le, hLq]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `k₁ q hqU1 i`. Rewrite using `[hLq, Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `k₂ q hqU2 i`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨hv, w, rfl⟩`. Establish `h1` using `map_mem_span_elim (e.restrictScalars (regAt ξ q)) f f' hfe hfe' (hspq ▸ hv)`.

Simplify `h1` using `[hee]`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `⟨?_, f i, hfe i⟩` and prove the remaining obligations. Rewrite using `[← hspq]`.

Conclude with `Submodule.subset_span ⟨Sum.inl i, rfl⟩`.
-/
theorem isVBOn_inter_range (L : Lat ξ E) (T : Set (Cpt ξ)) (g : ℕ) (e : E →ₗ[Ω] E) (he : e ∘ₗ e = e)
    (hVB : L.IsVBOn T g ⊤) (hs : ∀ p ∈ T, ∀ v ∈ L p, e v ∈ L p) :
    (L.inter (LinearMap.range e)).IsVBOn T (finrank Ω (LinearMap.range e)) (LinearMap.range e) := by
  intro p hp
  obtain ⟨U, hpU, b, hbs, hfr⟩ := hVB p hp
  obtain ⟨hbi, hbp⟩ := hfr p hp hpU
  haveI := isLocalRing_regAt p
  obtain ⟨r, r', f, f', hli, hsp, hsR, hfe, hfe'⟩ :=
    exists_frame_of_proj (regAt ξ p) (L p) b hbi hbs hbp e he (hs p hp)
  have hee : ∀ v, e (e v) = e v := fun v => LinearMap.congr_fun he v
  have hfli : LinearIndependent Ω f := by
    simpa using hli.comp _ Sum.inl_injective
  have hV : Submodule.span Ω (Set.range f) = LinearMap.range e := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨f i, hfe i⟩
    · rintro _ ⟨w, rfl⟩
      exact map_mem_span_elim e f f' hfe hfe' (hsp ▸ Submodule.mem_top)
  have hr : r = finrank Ω (LinearMap.range e) := by
    have := finrank_span_eq_card hfli
    rw [hV, Fintype.card_fin] at this
    exact this.symm
  subst hr
  obtain ⟨U₁, h₁, k₁⟩ := exists_open_mem_span p (Sum.elim f f') b (fun i => by
    rw [← hbp, ← hsR]
    exact Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨U₂, h₂, k₂⟩ := exists_open_mem_span p b (Sum.elim f f') (fun i => by
    rw [hsR, hbp]
    exact Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨U ⊓ U₁ ⊓ U₂, ⟨⟨hpU, h₁⟩, h₂⟩, f, hV, fun q hq hqU => ⟨hfli, ?_⟩⟩
  obtain ⟨⟨hqU0, hqU1⟩, hqU2⟩ := hqU
  have hLq : L q = Submodule.span (regAt ξ q) (Set.range b) := (hfr q hq hqU0).2
  have hspq : Submodule.span (regAt ξ q) (Set.range (Sum.elim f f')) = L q := by
    apply le_antisymm
    · rw [Submodule.span_le, hLq]
      rintro _ ⟨i, rfl⟩
      exact k₁ q hqU1 i
    · rw [hLq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact k₂ q hqU2 i
  apply le_antisymm
  · rintro _ ⟨hv, w, rfl⟩
    have h1 := map_mem_span_elim (e.restrictScalars (regAt ξ q)) f f' hfe hfe' (hspq ▸ hv)
    simpa [hee] using h1
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨?_, f i, hfe i⟩
    rw [← hspq]
    exact Submodule.subset_span ⟨Sum.inl i, rfl⟩

end Near

section Field

variable (F : Type) [Field F] [NumberField F]

/- English proof (translation)
Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := ℤ)` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `n hn`. Establish `h : σ (algebraMap ℤ (𝓞 F) n) = 0` using `hn`.

Simplify using `only [algebraMap_int_eq, eq_intCast, map_intCast, Int.cast_eq_zero] at h`. Simplify using `[h]`.
-/
theorem injective_of_charZero {Ω : Type} [Field Ω] [CharZero Ω] (σ : 𝓞 F →+* Ω) : Function.Injective σ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  have h : σ (algebraMap ℤ (𝓞 F) n) = 0 := hn
  simp only [algebraMap_int_eq, eq_intCast, map_intCast, Int.cast_eq_zero] at h
  simp [h]

/- English proof (translation)
Establish `h` using `Ideal.absNorm_mem (differentIdeal ℤ (𝓞 F))`. Rewrite `h` using `[NumberField.absNorm_differentIdeal F (𝓞 F)]`. Break down `Int.natAbs_eq (discr F) with h' | h'` into its components or cases. Establish `: ((discr F : ℤ) : 𝓞 F) = (((discr F).natAbs : ℕ) : 𝓞 F)` using `by conv_lhs => rw [h']`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `h`. Establish `: ((discr F : ℤ) : 𝓞 F) = -(((discr F).natAbs : ℕ) : 𝓞 F)` using `by conv_lhs => rw [h']`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `neg_mem h`.
-/
theorem discr_mem_differentIdeal : (((discr F : ℤ) : 𝓞 F)) ∈ differentIdeal ℤ (𝓞 F) := by
  have h := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 F))
  rw [NumberField.absNorm_differentIdeal F (𝓞 F)] at h
  rcases Int.natAbs_eq (discr F) with h' | h'
  · have : ((discr F : ℤ) : 𝓞 F) = (((discr F).natAbs : ℕ) : 𝓞 F) := by
      conv_lhs => rw [h']
      simp
    rw [this]; exact h
  · have : ((discr F : ℤ) : 𝓞 F) = -(((discr F).natAbs : ℕ) : 𝓞 F) := by
      conv_lhs => rw [h']
      simp
    rw [this]; exact neg_mem h

end Field

/- English proof (translation)
Introduce `X Ω _ ξ E _ _ F _ _ ρ L T g I _ σ _ hσ hcard _ hVB hst hreg hdisc`. Set `τ : I → (F →+* Ω)` to `fun s => IsFractionRing.lift (injective_of_charZero F (σ s))`. Establish `hτ : ∀ s (a : 𝓞 F), τ s (a : F) = σ s a` using `fun s a => IsFractionRing.lift_algebraMap (injective_of_charZero F (σ s)) a`. Establish `hτinj : Function.Injective τ`. Introduce `s t hst'`.

Apply `hσ` to reduce the goal to its premises. Use extensionality with `a`. Rewrite using `[← hτ, ← hτ, hst']`. Set `j : (F →+* Ω) → (F →ₐ[ℚ] AlgebraicClosure Ω)` to `fun φ => ((algebraMap Ω (AlgebraicClosure Ω)).comp φ).toRatAlgHom`. Establish `hj : Function.Injective j`.

Introduce `φ ψ hφψ`. Use extensionality with `x`. Apply `(algebraMap Ω (AlgebraicClosure Ω)).injective` to reduce the goal to its premises. Use `DFunLike.congr_fun hφψ x` as an intermediate fact. Simplify `this` using `[j]`.

Use `haveI : Finite (F →+* Ω) := Finite.of_injective j hj`. Use `letI : Fintype (F →+* Ω) := Fintype.ofFinite _`. Establish `hle : Fintype.card (F →+* Ω) ≤ finrank ℚ F`. Rewrite using `[← AlgHom.card ℚ F (AlgebraicClosure Ω)]`. Conclude with `Fintype.card_le_of_injective j hj`.

Establish `hge : finrank ℚ F ≤ Fintype.card (F →+* Ω)` using `hcard ▸ Fintype.card_le_of_injective τ hτinj`. Establish `hc : Fintype.card (F →+* Ω) = finrank ℚ F` using `le_antisymm hle hge`. Establish `hbij : Function.Bijective τ` using `(Fintype.bijective_iff_injective_and_card τ).2 ⟨hτinj, hcard.trans hc.symm⟩`. Establish `hsum : ∑ s, HT.eigProj ρ (τ s) = 1`. Rewrite using `[← HT.sum_eigProj_eq_one Ω E F ρ hc]`.

Conclude with `hbij.sum_comp fun φ => HT.eigProj ρ φ`. Establish `heig : ∀ s, eigSp ρ (σ s) = HT.eigSp ρ (τ s)`. Introduce `s`. Use extensionality with `v`. Simplify using `[GlobalTheory.CompanionTheory.Ar.eigSp, HT.eigSp, Submodule.mem_iInf, sub_eq_zero, hτ]`.

Establish `spec` using `fun s => HT.ProjEig.eigProj_spec Ω E F ρ (τ s)`. Establish `hrange : ∀ s, LinearMap.range (HT.eigProj ρ (τ s)) = eigSp ρ (σ s)`. Introduce `s`. Rewrite using `[heig]`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `(spec s).1 v`. Introduce `v hv`. Conclude with `⟨v, (spec s).2.1 v hv⟩`. Establish `hidem : ∀ s, HT.eigProj ρ (τ s) ∘ₗ HT.eigProj ρ (τ s) = HT.eigProj ρ (τ s)`.

Introduce `s`. Use extensionality with `v`. Conclude with `(spec s).2.1 _ ((spec s).1 v)`. Establish `hcoef : ∀ p ∈ T, ∀ s k, τ s (HT.dualInt F k) ∈ regAt ξ p`. Introduce `p hp s k`.

Take `⟨z, hz⟩` from `HT.exists_different_mul_dualInt F _ (discr_mem_differentIdeal F) k`. Take `⟨hd0, -, hdi⟩` from `hdisc p hp`. Establish `h1 : σ s z = ((discr F : ℤ) : Ω) * τ s (HT.dualInt F k)`. Rewrite using `[← hτ, hz, map_mul, hτ]`. Simplify using the standard rewrite rules.

Establish `h2 : τ s (HT.dualInt F k) = ((discr F : ℤ) : Ω)⁻¹ * σ s z`. Rewrite using `[h1, inv_mul_cancel_left₀ hd0]`. Rewrite using `[h2]`. Conclude with `mul_mem hdi (hreg p hp s z)`. Establish `hstable : ∀ p ∈ T, ∀ s, ∀ v ∈ L p, HT.eigProj ρ (τ s) v ∈ L p`.

Introduce `p hp s v hv`. Unfold `HT.eigProj`. Rewrite using `[LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Conclude with `Submodule.smul_mem (L p) (⟨_, hcoef p hp s k⟩ : regAt ξ p) (hst p hp _ v hv)`.

Use `⟨fun s => ?_, fun p hp => ?_⟩` and prove the remaining obligations. Rewrite using `[← hrange s]`. Conclude with `isVBOn_inter_range L T g _ (hidem s) hVB fun p hp => hstable p hp s`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `v hv`.

Establish `h1 : v = ∑ s, HT.eigProj ρ (τ s) v`. Rewrite using `[← LinearMap.sum_apply, hsum, Module.End.one_apply]`. Rewrite using `[h1]`. Use `Submodule.sum_mem _ fun s _ => ?_` and prove the remaining obligations. Use `Submodule.mem_iSup_of_mem s ⟨hstable p hp s v hv, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hrange s]`. Conclude with `⟨v, rfl⟩`. Conclude with `iSup_le fun s => inf_le_left`.
-/
theorem isVBOn_eigSp : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (F : Type) [Field F] [NumberField F] (ρ : NumberField.RingOfIntegers F →+* Module.End Ω E) (L : Lat ξ E) (T : Set (Cpt ξ)) (g : ℕ) (I : Type) [Fintype I] (σ : I → (NumberField.RingOfIntegers F →+* Ω)), IsCptGen ξ → Function.Injective σ → Fintype.card I = Module.finrank ℚ F → [CharZero Ω] → L.IsVBOn T g ⊤ → (∀ p ∈ T, ∀ a, ∀ e ∈ L p, ρ a e ∈ L p) → (∀ p ∈ T, ∀ s a, σ s a ∈ regAt ξ p) → (∀ p ∈ T, unitAt ξ p ((NumberField.discr F : ℤ) : Ω)) → (∀ s, (L.inter (eigSp ρ (σ s))).IsVBOn T (Module.finrank Ω (eigSp ρ (σ s))) (eigSp ρ (σ s))) ∧ ∀ p ∈ T, L p = ⨆ s, (L.inter (eigSp ρ (σ s))) p := by
  intro X Ω _ ξ E _ _ F _ _ ρ L T g I _ σ _ hσ hcard _ hVB hst hreg hdisc
  classical
  let τ : I → (F →+* Ω) := fun s => IsFractionRing.lift (injective_of_charZero F (σ s))
  have hτ : ∀ s (a : 𝓞 F), τ s (a : F) = σ s a := fun s a =>
    IsFractionRing.lift_algebraMap (injective_of_charZero F (σ s)) a
  have hτinj : Function.Injective τ := by
    intro s t hst'
    apply hσ
    ext a
    rw [← hτ, ← hτ, hst']
  let j : (F →+* Ω) → (F →ₐ[ℚ] AlgebraicClosure Ω) := fun φ =>
    ((algebraMap Ω (AlgebraicClosure Ω)).comp φ).toRatAlgHom
  have hj : Function.Injective j := by
    intro φ ψ hφψ
    ext x
    apply (algebraMap Ω (AlgebraicClosure Ω)).injective
    have := DFunLike.congr_fun hφψ x
    simpa [j] using this
  haveI : Finite (F →+* Ω) := Finite.of_injective j hj
  letI : Fintype (F →+* Ω) := Fintype.ofFinite _
  have hle : Fintype.card (F →+* Ω) ≤ finrank ℚ F := by
    rw [← AlgHom.card ℚ F (AlgebraicClosure Ω)]
    exact Fintype.card_le_of_injective j hj
  have hge : finrank ℚ F ≤ Fintype.card (F →+* Ω) := hcard ▸ Fintype.card_le_of_injective τ hτinj
  have hc : Fintype.card (F →+* Ω) = finrank ℚ F := le_antisymm hle hge
  have hbij : Function.Bijective τ :=
    (Fintype.bijective_iff_injective_and_card τ).2 ⟨hτinj, hcard.trans hc.symm⟩
  have hsum : ∑ s, HT.eigProj ρ (τ s) = 1 := by
    rw [← HT.sum_eigProj_eq_one Ω E F ρ hc]
    exact hbij.sum_comp fun φ => HT.eigProj ρ φ
  have heig : ∀ s, eigSp ρ (σ s) = HT.eigSp ρ (τ s) := by
    intro s
    ext v
    simp [GlobalTheory.CompanionTheory.Ar.eigSp, HT.eigSp, Submodule.mem_iInf, sub_eq_zero, hτ]
  have spec := fun s => HT.ProjEig.eigProj_spec Ω E F ρ (τ s)
  have hrange : ∀ s, LinearMap.range (HT.eigProj ρ (τ s)) = eigSp ρ (σ s) := by
    intro s
    rw [heig]
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact (spec s).1 v
    · intro v hv
      exact ⟨v, (spec s).2.1 v hv⟩
  have hidem : ∀ s, HT.eigProj ρ (τ s) ∘ₗ HT.eigProj ρ (τ s) = HT.eigProj ρ (τ s) := by
    intro s
    ext v
    exact (spec s).2.1 _ ((spec s).1 v)
  have hcoef : ∀ p ∈ T, ∀ s k, τ s (HT.dualInt F k) ∈ regAt ξ p := by
    intro p hp s k
    obtain ⟨z, hz⟩ := HT.exists_different_mul_dualInt F _ (discr_mem_differentIdeal F) k
    obtain ⟨hd0, -, hdi⟩ := hdisc p hp
    have h1 : σ s z = ((discr F : ℤ) : Ω) * τ s (HT.dualInt F k) := by
      rw [← hτ, hz, map_mul, hτ]
      simp
    have h2 : τ s (HT.dualInt F k) = ((discr F : ℤ) : Ω)⁻¹ * σ s z := by
      rw [h1, inv_mul_cancel_left₀ hd0]
    rw [h2]
    exact mul_mem hdi (hreg p hp s z)
  have hstable : ∀ p ∈ T, ∀ s, ∀ v ∈ L p, HT.eigProj ρ (τ s) v ∈ L p := by
    intro p hp s v hv
    unfold HT.eigProj
    rw [LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    exact Submodule.smul_mem (L p) (⟨_, hcoef p hp s k⟩ : regAt ξ p) (hst p hp _ v hv)
  refine ⟨fun s => ?_, fun p hp => ?_⟩
  · rw [← hrange s]
    exact isVBOn_inter_range L T g _ (hidem s) hVB fun p hp => hstable p hp s
  · apply le_antisymm
    · intro v hv
      have h1 : v = ∑ s, HT.eigProj ρ (τ s) v := by
        rw [← LinearMap.sum_apply, hsum, Module.End.one_apply]
      rw [h1]
      refine Submodule.sum_mem _ fun s _ => ?_
      refine Submodule.mem_iSup_of_mem s ⟨hstable p hp s v hv, ?_⟩
      rw [← hrange s]
      exact ⟨v, rfl⟩
    · exact iSup_le fun s => inf_le_left

end GlobalTheory.CompanionTheory.Ar.EigSplit
