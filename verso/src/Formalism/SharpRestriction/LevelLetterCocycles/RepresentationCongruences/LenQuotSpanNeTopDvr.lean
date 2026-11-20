import Formalism.SharpRestriction.LevelLetterCocycles.AdmBoundsBOfAdm
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColTwoStep

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

omit [Algebra O LL] in

/- English proof (translation)
Establish `hI : Ideal.span {t} ≠ ⊥` using `by rwa [Ne, Ideal.span_singleton_eq_bot]`. Establish `hA : IsArtinianRing (O ⧸ Ideal.span {t})`. Rewrite using `[isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[Ring.krullDimLE_zero_iff]`.

Introduce `J hJ`. Establish `hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {t}))` using `Ideal.Quotient.mk_surjective`. Establish `hJ' : (J.comap (Ideal.Quotient.mk (Ideal.span {t}))).IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hne : J.comap (Ideal.Quotient.mk (Ideal.span {t})) ≠ ⊥`. Introduce `h`.

Apply `hI` to reduce the goal to its premises. Rewrite using `[eq_bot_iff, ← h]`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]`. Conclude with `J.zero_mem`.

Establish `hmax` using `hJ'.isMaximal hne`. Use `⟨⟨hJ.ne_top, fun K hK => ?_⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hKtop`. Establish `hK' : K.comap (Ideal.Quotient.mk (Ideal.span {t})) ≠ ⊤` using `fun h => hKtop (by`. Rewrite using `[← Ideal.map_comap_of_surjective _ hsurj K, h, Ideal.map_top])`.

Establish `hle : J.comap (Ideal.Quotient.mk (Ideal.span {t})) ≤ K.comap (Ideal.Quotient.mk (Ideal.span {t}))` using `Ideal.comap_mono hK.le`. Establish `heq` using `hmax.eq_of_le hK' hle`. Apply `hK.ne` to reduce the goal to its premises. Rewrite using `[← Ideal.map_comap_of_surjective _ hsurj K, ← heq, Ideal.map_comap_of_surjective _ hsurj J]`. Rewrite using `[Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]`.

Use `haveI := hA`. Conclude with `⟨inferInstance, isArtinian_of_surjective_algebraMap (R := O ⧸ Ideal.span {t}) Ideal.Quotient.mk_surjective⟩`.
-/
theorem len_quot_span_ne_top_dvr [IsDomain O] [IsDiscreteValuationRing O] (t : O) (ht : t ≠ 0) :
    Module.length O (O ⧸ Ideal.span {t}) ≠ ⊤ := by
  have hI : Ideal.span {t} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hA : IsArtinianRing (O ⧸ Ideal.span {t}) := by
    rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
    refine ⟨inferInstance, ?_⟩
    rw [Ring.krullDimLE_zero_iff]
    intro J hJ
    have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {t})) :=
      Ideal.Quotient.mk_surjective
    have hJ' : (J.comap (Ideal.Quotient.mk (Ideal.span {t}))).IsPrime := Ideal.comap_isPrime _ _
    have hne : J.comap (Ideal.Quotient.mk (Ideal.span {t})) ≠ ⊥ := by
      intro h
      apply hI
      rw [eq_bot_iff, ← h]
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact J.zero_mem
    have hmax := hJ'.isMaximal hne
    refine ⟨⟨hJ.ne_top, fun K hK => ?_⟩⟩
    by_contra hKtop
    have hK' : K.comap (Ideal.Quotient.mk (Ideal.span {t})) ≠ ⊤ := fun h => hKtop (by
      rw [← Ideal.map_comap_of_surjective _ hsurj K, h, Ideal.map_top])
    have hle : J.comap (Ideal.Quotient.mk (Ideal.span {t})) ≤
        K.comap (Ideal.Quotient.mk (Ideal.span {t})) := Ideal.comap_mono hK.le
    have heq := hmax.eq_of_le hK' hle
    apply hK.ne
    rw [← Ideal.map_comap_of_surjective _ hsurj K, ← heq, Ideal.map_comap_of_surjective _ hsurj J]
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  haveI := hA
  exact ⟨inferInstance, isArtinian_of_surjective_algebraMap (R := O ⧸ Ideal.span {t})
    Ideal.Quotient.mk_surjective⟩

/- English proof (translation)
Take `⟨s, hs, hscard⟩` from `hgen`. Establish `hrep : ∀ x ∈ latticeFiniteCohomology PD T₂.L, ∃ y : G → T₂.V, ∃ hy : y ∈ latticeCocycles T₂.L, y ∈ latticeFiniteCocycles PD T₂.L ∧ Submodule.mkQ _ (⟨y, hy⟩ : latticeCocycles T₂.L) = x`. Introduce `x hx`. Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.1 hx`. Conclude with `⟨z.1, z.2, hz, rfl⟩`.

Set `r : LatticeCohomology T₂.L → (G → T₂.V)` to `fun x => if hx : x ∈ latticeFiniteCohomology PD T₂.L then (hrep x hx).choose else 0`. Set `s' : Finset (G → T₂.V)` to `s.image r`. Establish `hmemH : ∀ x ∈ s, x ∈ latticeFiniteCohomology PD T₂.L` using `fun x hx => hs ▸ Submodule.subset_span hx`. Establish `hrx : ∀ x (hx : x ∈ latticeFiniteCohomology PD T₂.L), r x = (hrep x hx).choose` using `fun x hx => by`. Simplify using `only [r, dif_pos hx]`.

Establish `hs'Z : (↑s' : Set (G → T₂.V)) ⊆ latticeFiniteCocycles PD T₂.L`. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hy`. Rewrite using `[hrx x (hmemH x hx)]`. Conclude with `(hrep x (hmemH x hx)).choose_spec.choose_spec.1`.

Establish `hB : latticeCoboundaries T₂.L ≤ F.ImF PD`. Unfold `LatHom.ImF`. Conclude with `le_sup_right`. Establish `hZZ : Submodule.span O (↑Z : Set (G → T₂.V)) ≤ latticeFiniteCocycles PD T₂.L` using `Submodule.span_le.2 (fun x hx => hZ x hx)`. Establish `hspan : Submodule.span O (↑s' : Set (G → T₂.V)) ⊔ (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L) = latticeFiniteCocycles PD T₂.L`.

Establish `hNle : Submodule.span O (↑s' : Set (G → T₂.V)) ⊔ (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L) ≤ latticeFiniteCocycles PD T₂.L` using `sup_le (Submodule.span_le.2 hs'Z) inf_le_right`. Use `le_antisymm hNle ?_` and prove the remaining obligations. Introduce `c hc`. Establish `hcZ1 : c ∈ latticeCocycles T₂.L` using `(Submodule.mem_inf.1 hc).1`. Establish `hq : Submodule.mkQ _ (⟨c, hcZ1⟩ : latticeCocycles T₂.L) ∈ latticeFiniteCohomology PD T₂.L` using `Submodule.mem_map_of_mem hc`.

Establish `hle : latticeFiniteCohomology PD T₂.L ≤ ((Submodule.span O (↑s' : Set (G → T₂.V)) ⊔ (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L)).comap (latticeCocycles T₂.L).subtype).map (Submodule.mkQ _)`. Rewrite using `[← hs, Submodule.span_le]`. Introduce `x hx`. Take `⟨hy, _, hyq⟩` from `(hrep x (hmemH x hx)).choose_spec`. Use `⟨⟨(hrep x (hmemH x hx)).choose, hy⟩, ?_, hyq⟩` and prove the remaining obligations.

Use `show (hrep x (hmemH x hx)).choose ∈ Submodule.span O (↑s' : Set (G → T₂.V)) ⊔ (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L)`. Apply `Submodule.mem_sup_left` to reduce the goal to its premises. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `Finset.mem_image.2 ⟨x, hx, ?_⟩` and prove the remaining obligations. Conclude with `hrx x (hmemH x hx)`.

Take `⟨y, hyN, hyq⟩` from `hle hq`. Establish `hyN' : (y : G → T₂.V) ∈ Submodule.span O (↑s' : Set (G → T₂.V)) ⊔ (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L)` using `hyN`. Rewrite `hyq` using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Establish `h2 : (y : G → T₂.V) - c ∈ latticeCoboundaries T₂.L` using `by simpa using Submodule.mem_comap.1 hyq`. Establish `hd : c - (y : G → T₂.V) ∈ latticeCoboundaries T₂.L`.

Establish `h3` using `(latticeCoboundaries T₂.L).neg_mem h2`. Simplify using `using h3`. Establish `hyZ : (y : G → T₂.V) ∈ latticeFiniteCocycles PD T₂.L` using `hNle hyN'`. Establish `hdI : c - (y : G → T₂.V) ∈ F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L` using `Submodule.mem_inf.2 ⟨hB hd, (latticeFiniteCocycles PD T₂.L).sub_mem hc hyZ⟩`. Establish `e1 : c = (y : G → T₂.V) + (c - (y : G → T₂.V))` using `by abel`.

Rewrite using `[e1]`. Conclude with `Submodule.add_mem _ hyN' (Submodule.mem_sup_right hdI)`. Establish `hexp : ∀ q ∈ latticeFiniteCocycles PD T₂.L, (PD.p ^ e : ℕ) • q ∈ Submodule.span O (↑Z : Set (G → T₂.V)) ⊔ (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L)`. Introduce `q hq`. Establish `h` using `he q hq`.

Take `⟨i, hi, z, hz, hiz⟩` from `Submodule.mem_sup.1 h`. Establish `hzZ : z ∈ latticeFiniteCocycles PD T₂.L` using `hZZ hz`. Rewrite using `[← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, ← hiz]`. Establish `hiZ : i ∈ latticeFiniteCocycles PD T₂.L`. Establish `e2 : i = ((PD.p : O) ^ e) • q - z` using `by rw [← hiz]; abel`.

Rewrite using `[e2]`. Conclude with `(latticeFiniteCocycles PD T₂.L).sub_mem ((latticeFiniteCocycles PD T₂.L).smul_mem _ hq) hzZ`. Rewrite using `[add_comm]`. Conclude with `Submodule.add_mem_sup hz (Submodule.mem_inf.2 ⟨hi, hiZ⟩)`. Establish `hlift : ∀ q ∈ Submodule.span O (↑Z : Set (G → T₂.V)), (PD.p ^ e' : ℕ) • q ∈ F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L`.

Introduce `q hq`. Establish `hqZ : q ∈ latticeFiniteCocycles PD T₂.L` using `hZZ hq`. Rewrite using `[← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]`. Conclude with `Submodule.mem_inf.2 ⟨hL q hqZ, (latticeFiniteCocycles PD T₂.L).smul_mem _ hqZ⟩`. Establish `key` using `Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds.length_quotient_le_of_two_step O (G → T₂.V) PD.p g₁ Z.card e e' (latticeFiniteCocycles PD T₂.L) (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L) s' Z inf_le_right (Finset.card_image_le.trans hscard) le_rfl (fun z hz => hZ …`.

Establish `hcomap : (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L).comap (latticeFiniteCocycles PD T₂.L).subtype = (F.ImF PD).comap (latticeFiniteCocycles PD T₂.L).subtype`. Rewrite using `[Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]`. Rewrite `key` using `[hcomap]`. Establish `hcol : F.col PD ≤ ((g₁ * e + Z.card * e' : ℕ) : ℕ∞) * lenOl PD (O` using `O) := key`. Establish `hlen : lenOl PD (O` using `O) ≠ ⊤ := len_quot_span_ne_top_dvr (O := O) _ hp0`.

Take `⟨k, hk⟩` from `ENat.ne_top_iff_exists.1 hlen`. Rewrite `hcol` using `[← hk, ← Nat.cast_mul]`. Establish `hcolfin : F.col PD ≠ ⊤` using `fun h => ENat.coe_ne_top _ (top_le_iff.1 (h ▸ hcol))`. Take `⟨mm, hmm⟩` from `ENat.ne_top_iff_exists.1 hcolfin`. Use `⟨mm, k, hmm.symm, hk.symm, ?_⟩` and prove the remaining obligations.

Rewrite `hcol` using `[← hmm]`. Establish `h4 : mm ≤ (g₁ * e + Z.card * e') * k` using `by exact_mod_cast hcol`. Establish `h5 : (mm : ℝ) ≤ (((g₁ * e + Z.card * e') * k : ℕ) : ℝ)` using `by exact_mod_cast h4`. Move the coercions through the operations in `at h5`. Conclude with `h5`.
-/
theorem colLeR_of_exponent [IsDomain O] [IsDiscreteValuationRing O] (PD : PeriodData G Qp K₀ K B BdR)
    (hp0 : ((PD.p : ℕ) : O) ≠ 0) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (g₁ e e' : ℕ)
    (hgen : ∃ s : Finset (LatticeCohomology T₂.L), Submodule.span O (s : Set (LatticeCohomology T₂.L)) = latticeFiniteCohomology PD T₂.L ∧
      s.card ≤ g₁)
    (Z : Finset (G → T₂.V)) (hZ : ∀ z ∈ Z, z ∈ latticeFiniteCocycles PD T₂.L)
    (he : ExpIn PD F Z e)
    (hL : F.LiftF PD e') :
    TruncatedSeriesCountingBounds.ColLeR PD F ((g₁ : ℝ) * e + (Z.card : ℝ) * e') := by
  classical
  obtain ⟨s, hs, hscard⟩ := hgen
  have hrep : ∀ x ∈ latticeFiniteCohomology PD T₂.L, ∃ y : G → T₂.V, ∃ hy : y ∈ latticeCocycles T₂.L,
      y ∈ latticeFiniteCocycles PD T₂.L ∧ Submodule.mkQ _ (⟨y, hy⟩ : latticeCocycles T₂.L) = x := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hx
    exact ⟨z.1, z.2, hz, rfl⟩
  let r : LatticeCohomology T₂.L → (G → T₂.V) := fun x =>
    if hx : x ∈ latticeFiniteCohomology PD T₂.L then (hrep x hx).choose else 0
  let s' : Finset (G → T₂.V) := s.image r
  have hmemH : ∀ x ∈ s, x ∈ latticeFiniteCohomology PD T₂.L := fun x hx => hs ▸ Submodule.subset_span hx
  have hrx : ∀ x (hx : x ∈ latticeFiniteCohomology PD T₂.L), r x = (hrep x hx).choose := fun x hx => by
    simp only [r, dif_pos hx]
  have hs'Z : (↑s' : Set (G → T₂.V)) ⊆ latticeFiniteCocycles PD T₂.L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    rw [hrx x (hmemH x hx)]
    exact (hrep x (hmemH x hx)).choose_spec.choose_spec.1
  have hB : latticeCoboundaries T₂.L ≤ F.ImF PD := by
    unfold LatHom.ImF
    exact le_sup_right
  have hZZ : Submodule.span O (↑Z : Set (G → T₂.V)) ≤ latticeFiniteCocycles PD T₂.L :=
    Submodule.span_le.2 (fun x hx => hZ x hx)
  have hspan : Submodule.span O (↑s' : Set (G → T₂.V)) ⊔ (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L) = latticeFiniteCocycles PD T₂.L := by
    have hNle : Submodule.span O (↑s' : Set (G → T₂.V)) ⊔ (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L) ≤ latticeFiniteCocycles PD T₂.L :=
      sup_le (Submodule.span_le.2 hs'Z) inf_le_right
    refine le_antisymm hNle ?_
    intro c hc
    have hcZ1 : c ∈ latticeCocycles T₂.L := (Submodule.mem_inf.1 hc).1
    have hq : Submodule.mkQ _ (⟨c, hcZ1⟩ : latticeCocycles T₂.L) ∈ latticeFiniteCohomology PD T₂.L := Submodule.mem_map_of_mem hc
    have hle : latticeFiniteCohomology PD T₂.L ≤ ((Submodule.span O (↑s' : Set (G → T₂.V)) ⊔
        (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L)).comap (latticeCocycles T₂.L).subtype).map (Submodule.mkQ _) := by
      rw [← hs, Submodule.span_le]
      intro x hx
      obtain ⟨hy, _, hyq⟩ := (hrep x (hmemH x hx)).choose_spec
      refine ⟨⟨(hrep x (hmemH x hx)).choose, hy⟩, ?_, hyq⟩
      show (hrep x (hmemH x hx)).choose ∈ Submodule.span O (↑s' : Set (G → T₂.V)) ⊔
        (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L)
      apply Submodule.mem_sup_left
      apply Submodule.subset_span
      refine Finset.mem_image.2 ⟨x, hx, ?_⟩
      exact hrx x (hmemH x hx)
    obtain ⟨y, hyN, hyq⟩ := hle hq
    have hyN' : (y : G → T₂.V) ∈ Submodule.span O (↑s' : Set (G → T₂.V)) ⊔
        (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L) := hyN
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hyq
    have h2 : (y : G → T₂.V) - c ∈ latticeCoboundaries T₂.L := by simpa using Submodule.mem_comap.1 hyq
    have hd : c - (y : G → T₂.V) ∈ latticeCoboundaries T₂.L := by
      have h3 := (latticeCoboundaries T₂.L).neg_mem h2
      simpa using h3
    have hyZ : (y : G → T₂.V) ∈ latticeFiniteCocycles PD T₂.L := hNle hyN'
    have hdI : c - (y : G → T₂.V) ∈ F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L :=
      Submodule.mem_inf.2 ⟨hB hd, (latticeFiniteCocycles PD T₂.L).sub_mem hc hyZ⟩
    have e1 : c = (y : G → T₂.V) + (c - (y : G → T₂.V)) := by abel
    rw [e1]
    exact Submodule.add_mem _ hyN' (Submodule.mem_sup_right hdI)
  have hexp : ∀ q ∈ latticeFiniteCocycles PD T₂.L, (PD.p ^ e : ℕ) • q ∈
      Submodule.span O (↑Z : Set (G → T₂.V)) ⊔ (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L) := by
    intro q hq
    have h := he q hq
    obtain ⟨i, hi, z, hz, hiz⟩ := Submodule.mem_sup.1 h
    have hzZ : z ∈ latticeFiniteCocycles PD T₂.L := hZZ hz
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, ← hiz]
    have hiZ : i ∈ latticeFiniteCocycles PD T₂.L := by
      have e2 : i = ((PD.p : O) ^ e) • q - z := by rw [← hiz]; abel
      rw [e2]
      exact (latticeFiniteCocycles PD T₂.L).sub_mem ((latticeFiniteCocycles PD T₂.L).smul_mem _ hq) hzZ
    rw [add_comm]
    exact Submodule.add_mem_sup hz (Submodule.mem_inf.2 ⟨hi, hiZ⟩)
  have hlift : ∀ q ∈ Submodule.span O (↑Z : Set (G → T₂.V)), (PD.p ^ e' : ℕ) • q ∈
      F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L := by
    intro q hq
    have hqZ : q ∈ latticeFiniteCocycles PD T₂.L := hZZ hq
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
    exact Submodule.mem_inf.2 ⟨hL q hqZ, (latticeFiniteCocycles PD T₂.L).smul_mem _ hqZ⟩
  have key := Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds.length_quotient_le_of_two_step O (G → T₂.V) PD.p g₁ Z.card e e' (latticeFiniteCocycles PD T₂.L)
    (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L) s' Z inf_le_right (Finset.card_image_le.trans hscard) le_rfl
    (fun z hz => hZ z hz) hspan hexp hlift
  have hcomap : (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L).comap (latticeFiniteCocycles PD T₂.L).subtype =
      (F.ImF PD).comap (latticeFiniteCocycles PD T₂.L).subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  rw [hcomap] at key
  have hcol : F.col PD ≤ ((g₁ * e + Z.card * e' : ℕ) : ℕ∞) * lenOl PD (O := O) := key
  have hlen : lenOl PD (O := O) ≠ ⊤ := len_quot_span_ne_top_dvr (O := O) _ hp0
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hlen
  rw [← hk, ← Nat.cast_mul] at hcol
  have hcolfin : F.col PD ≠ ⊤ := fun h => ENat.coe_ne_top _ (top_le_iff.1 (h ▸ hcol))
  obtain ⟨mm, hmm⟩ := ENat.ne_top_iff_exists.1 hcolfin
  refine ⟨mm, k, hmm.symm, hk.symm, ?_⟩
  rw [← hmm] at hcol
  have h4 : mm ≤ (g₁ * e + Z.card * e') * k := by exact_mod_cast hcol
  have h5 : (mm : ℝ) ≤ (((g₁ * e + Z.card * e') * k : ℕ) : ℝ) := by exact_mod_cast h4
  push_cast at h5
  exact h5

end Core

end Formalism.MainNotions.N.Ln17
